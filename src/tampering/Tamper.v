(** Tamper properties *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import Lia List ListSet.
Import ListNotations.

Require Import Copland DataFlow Index Graph Label Path Preamble Prefix.

Set Implicit Arguments.

(** * Definition 12: Local path%\index{Definition 12: Local path}% *)

Section Local.

  Variable L : lbls.

  (** The local property for event sequences over [lbls] *)

  Definition local (p : plc) (pi : evt_seq L) : Prop :=
    forall (i : idx pi),
      (0 < idx_nat i < length pi - 1 ->
       sendp (nth_safe L (nth_safe pi i)) = p
       /\ recvp (nth_safe L (nth_safe pi i)) = p)
      /\ (idx_nat i = 0 \/ idx_nat i = length pi - 1 ->
          sendp (nth_safe L (nth_safe pi i)) = p
          \/ recvp (nth_safe L (nth_safe pi i)) = p).

  Definition is_local pi := exists p, local p pi.

  (** The [local'] property is an equivalent, inductive alternative to
      [local].  We prove equivalence below. *)

  Inductive local' (p : plc) : evt_seq L -> Prop :=
  | local_nil : local' p []
  | local_sngl :
    forall v,
      sendp (nth_safe L v) = p \/ recvp (nth_safe L v) = p -> local' p [v]
  | local_dbl :
    forall v v',
      sendp (nth_safe L v') = p \/ recvp (nth_safe L v') = p ->
      sendp (nth_safe L v) = p \/ recvp (nth_safe L v) = p ->
      local' p [v; v']
  | local_step :
    forall pi v v' v'',
      local' p (v' :: v'' :: pi) ->
      sendp (nth_safe L v') = p ->
      recvp (nth_safe L v') = p ->
      sendp (nth_safe L v) = p \/ recvp (nth_safe L v) = p ->
      local' p (v :: v' :: v'' :: pi).

  Lemma local_iff_local' :
    forall p pi, local p pi <-> local' p pi.
  Proof.
    unfold local; split.
    - induction pi as [|v pi]; intros.
      + apply local_nil.
      + destruct pi as [|v' [|v'' pi]].
        * assert (0 < length [v]) by (simpl; lia).
          specialize H with (to_idx H0).
          destruct H as [_ H]. simpl in H.
          apply local_sngl; auto.
        * assert (0 < length [v; v']) by (simpl; lia).
          assert (1 < length [v; v']) by (simpl; lia).
          specialize H with (to_idx H0) as Hi0.
          specialize H with (to_idx H1) as Hi1.
          destruct Hi0 as [_ Hi0]; destruct Hi1 as [_ Hi1].
          apply local_dbl; auto.
        * assert (1 < length (v :: v' :: v'' :: pi)) by (simpl; lia).
          assert (nth_safe (v :: v' :: v'' :: pi) (to_idx H0) = v') by auto.
          specialize H with (to_idx H0) as Hv'. destruct Hv' as [Hv' _].
          apply local_step.
          -- apply IHpi. intros.
             rewrite (to_idx_nat_evi i) in *.
             destruct i as [n Hn]; simpl idx_evi.
             assert (HSn : S n < length (v :: v' :: v'' :: pi))
               by (simpl in *; lia).
             specialize H with (to_idx HSn) as [H H'].
             split; intros; rewrite <- (nth_safe_cons HSn).
             ++ apply H. simpl in *; lia.
             ++ destruct H2.
                ** simpl in H2; subst.
                   left. apply H; simpl; lia.
                ** apply H'; right; simpl in *; lia.
          -- rewrite <- H1. apply Hv'. simpl; lia.
          -- rewrite <- H1. apply Hv'. simpl; lia.
          -- assert (0 < length (v :: v' :: v'' :: pi)) by (simpl; lia).
             assert (nth_safe (v :: v' :: v'' :: pi) (to_idx H2) = v) by auto.
             specialize H with (to_idx H2) as [_ H].
             rewrite <- H3; auto.
    - intro. induction H; intros.
      + destruct i; simpl in *; lia.
      + pose proof (idx_sngl i).
        rewrite H0; split; try (simpl; intros; lia).
        rewrite nth_safe_sngl. auto.
      + rewrite (to_idx_nat_evi i).
        destruct i as [n Hn]; simpl idx_evi; simpl idx_nat.
        split; intro H1; simpl in H1; try lia.
        destruct H1; subst; simpl; auto.
      + rewrite (to_idx_nat_evi i).
        destruct i as [n Hn]; simpl idx_evi; simpl idx_nat.
        split; intros.
        * destruct n; try lia. destruct n.
          -- simpl. auto.
          -- assert (S n < length (v' :: v'' :: pi)) by (simpl in *; lia).
             assert (
                 0 < S n < length (v' :: v'' :: pi) - 1
               ) by (simpl in *; lia).
             assert (
                 nth_safe (v :: v' :: v'' :: pi) (to_idx Hn) =
                   nth_safe (v' :: v'' :: pi) (to_idx H4)
               ) by (rewrite <- (nth_safe_cons Hn); auto).
             specialize IHlocal' with (to_idx H4) as [IH _].
             rewrite H6. auto.
        * destruct H3; subst; auto.
          assert (
              Hn' : length (v' :: v'' :: pi) - 1 < length (v' :: v'' :: pi)
            ) by (simpl; lia).
          assert (
              S (length (v' :: v'' :: pi) - 1) < length (v :: v' :: v'' :: pi)
            ) by (simpl; lia).
          assert (
              nth_safe (v :: v' :: v'' :: pi) (to_idx Hn) =
                nth_safe (v' :: v'' :: pi) (to_idx Hn')
            ). {
            rewrite <- (nth_safe_cons H0).
            apply nth_safe_nat_eq. auto.
          }
          specialize IHlocal' with (to_idx Hn') as [_ IH].
          rewrite H3. auto.
  Qed.

  (** A local event sequence is local to the sending or receiving
      place of its last element. *)

  Lemma local_lst_plcs : forall p pi v,
      local p pi ->
      lst_elem pi v ->
      p = sendp (nth_safe L v) \/ p = recvp (nth_safe L v).
  Proof.
    intros p pi v H [i [H0 H1]].
    unfold local in H.
    specialize H with (i := i) as [H H'].
    subst; rewrite H0 in H'. intuition.
  Qed.

  (** Removing an element from the front of a local path does not
      change this property. *)

  Lemma local_cons :
    forall p pi v, local p (v :: pi) -> local p pi.
  Proof.
    intros. rewrite local_iff_local' in *.
    inv H; try constructor; auto.
  Qed.

  (** An event sequence is [local] iff its reverse is. *)

  Lemma local_implies_rev_local :
    forall p pi, local p pi -> local p (rev pi).
  Proof.
    unfold local.
    destruct pi as [|a pi]; intros;
      try (destruct i; simpl in *; lia).
    pose proof (rev_idx_preimage _ i) as [i' Hi]. subst.
    rewrite (to_idx_nat_evi i') in *.
    destruct i' as [n Hn]. simpl idx_evi.
    assert (
        n = 0 \/ 0 < n < length (a :: pi) - 1 \/ n = length (a :: pi) - 1
      ) by lia.
    destruct H0 as [H0|[H0|H0]]; subst.
    - split; intros.
      + simpl in H0.
        rewrite app_length in H0.
        rewrite rev_length in H0.
        simpl in H0; lia.
      + assert (
            length pi = 0 \/ length (a :: pi) - 1 = length (rev (a :: pi)) - 1
          ) by (simpl in *; lia).
        specialize H with (to_idx Hn).
        destruct H as [_ H]. simpl in H.
        rewrite nth_safe_rev. intuition.
    - assert (
          0 < idx_nat (rev_idx (to_idx Hn)) < length (rev (a :: pi)) - 1
        ). {
        simpl in Hn, H0; simpl.
        destruct n; try lia.
        rewrite app_length.
        rewrite rev_length.
        simpl; lia.
      }
      split; intros; try (simpl in *; lia).
      specialize H with (to_idx Hn).
      destruct H as [H _]. simpl idx_nat in H.
      apply H in H0. rewrite nth_safe_rev. intuition.
    - (* simpl goes too far here *)
      assert (idx_nat (rev_idx (to_idx Hn)) = 0). {
        assert (
            idx_nat (rev_idx (to_idx Hn))
            = length (a :: pi) - (idx_nat (to_idx Hn)) - 1
          ) by auto. rewrite H0.
        replace (idx_nat (to_idx Hn))
          with (length (a :: pi) - 1); auto. lia.
      }
      specialize H with (to_idx Hn).
      destruct H as [_ H].
      split; intros.
      + simpl in H0, H1; rewrite H0 in H1; lia.
      + rewrite nth_safe_rev. intuition.
  Qed.

  Lemma rev_local_implies_local :
    forall p pi, local p (rev pi) -> local p pi.
  Proof.
    intros. rewrite <- rev_involutive.
    apply local_implies_rev_local; auto.
  Qed.

  (** A [rev_no_teleport] event sequence is local iff all of its
      cross-place communication events are initial or terminal. *)

  Lemma is_local_xplc_comm_evt :
    forall pi,
      rev_no_teleport pi ->
      is_local pi <->
        forall i,
          xplc_comm_lbl (nth_safe L (nth_safe pi i)) ->
          idx_nat i = 0 \/ idx_nat i = length pi - 1.
  Proof.
    unfold is_local; split.
    - induction pi; intros;
        try (destruct i; simpl in *; lia).
      rewrite (to_idx_nat_evi i) in *.
      destruct i as [n Hn];
        simpl idx_evi in *; simpl idx_nat.
      destruct n; auto. right.
      assert (n < length pi) by (simpl in *; lia).
      assert (
          xplc_comm_lbl (nth_safe L (nth_safe pi (to_idx H2)))
        ) by (rewrite <- (nth_safe_cons Hn); auto).
      apply rev_no_teleport_cons in H.
      destruct H0 as [p H0].
      apply local_cons in H0 as H0'.
      assert (exists q, local q pi) by eauto.
      pose proof (IHpi H H4 _ H3); clear IHpi.
      destruct H5; try (simpl in *; lia).
      rewrite local_iff_local' in H0, H0'.
      assert (
          fst_elem pi (nth_safe pi (to_idx H2))
        ) by (eexists; eauto).
      inv H0'; try (simpl in *; lia);
        simpl in H5; subst n; simpl in *;
        inversion H0; [
          rewrite <- H14 in H13 |
          rewrite <- H15 in H14
        ]; contradiction.
    - induction pi; intros.
      + exists String.EmptyString.
        rewrite local_iff_local'.
        constructor.
      + apply rev_no_teleport_cons in H as H'.
        pose proof (IHpi H').
        assert (
            forall i : idx pi,
              xplc_comm_lbl (nth_safe L (nth_safe pi i)) ->
              idx_nat i = 0 \/ idx_nat i = length pi - 1
          ). {
          intros. rewrite (to_idx_nat_evi i) in *.
          destruct i as [n Hn];
            simpl idx_evi in *; simpl idx_nat.
          assert (S n < length (a :: pi)) by (simpl; lia).
          rewrite <- (nth_safe_cons H3) in H2.
          apply H0 in H2. simpl in H2; lia.
        }
        apply H1 in H2 as [p H2].
        destruct pi as [|a' [|a'' pi]].
        * exists (sendp (nth_safe L a)).
          rewrite local_iff_local' in *.
          constructor; auto.
        * exists (recvp (nth_safe L a')).
          rewrite local_iff_local' in *.
          inv H2. constructor; auto.
          assert (0 < length [a; a']) by (simpl; lia).
          assert (1 < length [a; a']) by (simpl; lia).
          assert (a = nth_safe [a; a'] (to_idx H2)) by auto.
          assert (a' = nth_safe [a; a'] (to_idx H3)) by auto.
          left. symmetry. rewrite H5.
          replace (nth_safe L a') with (
              (nth_safe L (nth_safe [a; a'] (to_idx H3)))
            ) by (rewrite H5; auto).
          apply H. auto.
        * exists p. rewrite local_iff_local' in *.
          assert (sendp (nth_safe L a') = recvp (nth_safe L a')). {
            rewrite <- not_xplc_comm_lbl; intro.
            assert (1 < length (a :: a' :: a'' :: pi)) by (simpl; lia).
            assert (a' = nth_safe _ (to_idx H4)) by auto.
            rewrite H5 in H3. apply H0 in H3. simpl in H3; lia.
          }
          constructor; auto; inv H2.
          -- destruct H8; auto. rewrite H3; auto.
          -- destruct H10; auto. rewrite H3; auto.
          -- destruct H8; auto. rewrite <- H3; auto.
          -- destruct H10; auto. rewrite <- H3; auto.
          -- assert (0 < length [a; a'; a'']) by (simpl; lia).
             assert (1 < length [a; a'; a'']) by (simpl; lia).
             assert (a = nth_safe _ (to_idx H2)) by auto.
             assert (a' = nth_safe _ (to_idx H4)) by auto.
             left. rewrite H3 in H8. symmetry.
             destruct H8; rewrite <- H8; rewrite H5;
               replace (nth_safe L a') with (
                 nth_safe L (nth_safe _ (to_idx H4))
               ) by (rewrite H7; auto); apply H; auto.
          -- assert (0 < length (a :: a' :: a'' :: v'' :: pi0)) by (simpl; lia).
             assert (1 < length (a :: a' :: a'' :: v'' :: pi0)) by (simpl; lia).
             assert (a = nth_safe _ (to_idx H2)) by auto.
             assert (a' = nth_safe _ (to_idx H4)) by auto.
             left. rewrite H3 in H10. symmetry.
             destruct H10 as [H10|H10];
               rewrite <- H10; rewrite H5;
               replace (nth_safe L a') with (
                 nth_safe L (nth_safe _ (to_idx H4))
               ) by (rewrite H6; auto); apply H; auto.
  Qed.

End Local.

(** * Definition 7: Place-signing path%\index{Definition 7: Place-signing path}% *)

Section PSigning.

  Variable L : lbls.

  (** The p-signing property for event sequences over [lbls] *)

  Definition p_signing (p : plc) (pi : evt_seq L) : Prop :=
    forall (i : idx pi) l,
      l = nth_safe L (nth_safe pi i) -> sig_lbl l -> sendp l = p.

  (** An equivalent inductive definition of p-signing *)

  Inductive p_signing' (p : plc) : evt_seq L -> Prop :=
  | ps_base : p_signing' p []
  | ps_sign :
    forall pi v,
      p_signing' p pi ->
      sig_lbl (nth_safe L v) ->
      sendp (nth_safe L v) = p ->
      p_signing' p (v :: pi)
  | ps_rest :
    forall pi v,
      p_signing' p pi ->
      ~(sig_lbl (nth_safe L v)) ->
      p_signing' p (v :: pi).

  (** Removing an initial element from a p-signing path does not
      affect this property. *)

  Lemma p_signing_cons :
    forall p pi v, p_signing p (v :: pi) -> p_signing p pi.
  Proof.
    unfold p_signing; intros.
    rewrite (to_idx_nat_evi i) in *.
    destruct i as [n Hn]. simpl in H0.
    assert (S n < length (v :: pi)) by (simpl; lia).
    apply (H (to_idx H2)); auto.
    rewrite <- (nth_safe_cons H2) in H0; auto.
  Qed.

  Lemma p_signing_iff_p_signing' :
    forall p pi, p_signing p pi <-> p_signing' p pi.
  Proof.
    split.
    - induction pi; intros; try apply ps_base.
      destruct (sig_lblb (nth_safe L a)) eqn:H'.
      + apply sig_lbl_reflect in H'.
        assert (0 < length (a :: pi)) by (simpl; lia).
        assert (nth_safe (a :: pi) (to_idx H0) = a) by auto.
        apply (H (to_idx H0)) in H' as H'';
          try (rewrite <- H1; auto); rewrite H1.
        apply p_signing_cons in H; apply IHpi in H.
        apply ps_sign; auto.
      + apply Bool.not_true_iff_false in H'.
        rewrite <- sig_lbl_reflect in H'.
        apply p_signing_cons in H.
        apply ps_rest; auto.
    - unfold p_signing; intros H i.
      rewrite (to_idx_nat_evi i).
      destruct i as [n Hn]. simpl.
      generalize dependent n.
      induction H; intros;
        try (simpl in *; lia);
        assert (H' : n = 0 \/ 0 < n) by lia;
        destruct H'; subst;
        try (simpl in H3; auto);
        try (simpl in H2; contradiction);
        destruct n; try lia;
        assert (n < length pi) by (simpl in *; lia);
        apply (IHp_signing' _ H1); auto;
        rewrite <- (nth_safe_cons Hn); auto.
  Qed.

  (** A path is p-signing iff its reverse is. *)

  Lemma p_signing_rev :
    forall p pi, p_signing p pi <-> p_signing p (rev pi).
  Proof.
    unfold p_signing; split; intros.
    - rewrite <- nth_safe_rev with (i := i) in H0.
      rewrite (to_idx_nat_evi (rev_idx i)) in *.
      destruct (rev_idx i) as [n Hn]. simpl in H0.
      generalize dependent n.
      rewrite rev_involutive; intros.
      eapply H; eauto.
    - rewrite <- nth_safe_rev with (i := i) in H0.
      eapply H; eauto.
  Qed.

End PSigning.

(** * Definition 8: Tamper-permitting paths%\index{Definition 8: Tamper-permitting paths}% *)

Section TmprPaths.

  Variable L : lbls.
  Variable G : io_graph L.

  (** The property that, when paired with [accm], makes for a
      tamper-permitting event sequence over [lbls]. *)

  Definition tmpr' (pi : evt_seq L) v v' : Prop :=
    fst_elem pi v
    /\ lst_elem pi v'
    /\ meas_lbl (nth_safe L v)
    /\ v <> v'
    /\ (p_signing (sendp (nth_safe L v')) pi \/ p_signing (recvp (nth_safe L v')) pi).

  Definition tmpr pi v v' := accm pi /\ tmpr' pi v v'.

  (** Tamper-permitting paths through IO graphs over [lbls] *)

  Definition tmpr_path pi v v' := io_path G pi /\ tmpr pi v v'.

  (** As with reversed paths, it is useful to have reversed tamper
      definitions. *)

  Definition rev_tmpr' (pi : evt_seq L) v' v : Prop :=
    lst_elem pi v
    /\ fst_elem pi v'
    /\ meas_lbl (nth_safe L v)
    /\ v <> v'
    /\ (p_signing (sendp (nth_safe L v')) pi \/ p_signing (recvp (nth_safe L v')) pi).

  (** An event sequence is [tmpr'] iff its [rev] reverse is
      [rev_tmpr']. *)

  Lemma tmpr'_iff_rev_tmpr'_rev :
    forall pi v v',
      tmpr' pi v v' <-> rev_tmpr' (rev pi) v' v.
  Proof with auto.
    unfold tmpr', rev_tmpr'.
    split; intros;
      destruct H as [H0 [H1 [H2 [H3 H4]]]];
      repeat split...
    - rewrite <- (rev_involutive pi).
      rewrite <- fst_lst_rev.
      rewrite rev_involutive...
    - rewrite fst_lst_rev.
      rewrite rev_involutive...
    - repeat rewrite <- p_signing_rev...
    - apply fst_lst_rev...
    - rewrite <- (rev_involutive pi).
      rewrite <- fst_lst_rev...
    - repeat rewrite (p_signing_rev _ pi)...
  Qed.

End TmprPaths.

(** * Lemma 2: Local Path Tampers%\index{Lemma 2: Local Path Tampers}% *)

Section LocalPathTmpr.

  Variable L : lbls.

  (** A local path is p-signing *)

  Lemma local_is_p_signing : forall p (pi : evt_seq L),
      local p pi -> p_signing p pi.
  Proof.
    unfold local, p_signing; intros.
    destruct H1 as [q [e H1]].
    rewrite H1. subst; simpl.
    specialize H with (i := i) as [H H'].
    rewrite H1 in H, H'.
    destruct i as [n Hn]; simpl in *.
    assert (
        (0 < n < length pi - 1) \/ (n = 0 \/ n = length pi - 1)
      ) by lia.
    destruct H0; intuition.
  Qed.

  (** A local path that meets all of the [tmpr'] conditions except the
      [p_signing] one in fact meets them all. *)

  Theorem local_path_tmprs : forall pi v v',
      fst_elem pi v ->
      lst_elem pi v' ->
      meas_lbl (nth_safe L v) ->
      v <> v' ->
      is_local pi ->
      tmpr' pi v v'.
  Proof.
    unfold tmpr'; intuition.
    destruct H3 as [p H3].
    pose proof (local_lst_plcs H3 H0).
    destruct H4; subst;
      apply local_is_p_signing in H3;
      [left | right]; auto.
  Qed.

End LocalPathTmpr.

(** * Definition 9: Tamper strategies%\index{Definition 9: Tamper strategies}% *)

Section TmprStgy.

  Variable L : lbls.
  Variable G : io_graph L.

  (** A set of events from [G] *)

  Definition evt_set := set (idx L).

  Definition tmpr_stgy v (V : evt_set) :=
    forall pi,
      io_path G pi ->
      fst_elem pi v ->
      lst_elem pi (io_output_evt G) ->
      exists v'' i,
        In v'' V
        /\ nth_safe pi i = v''
        /\ tmpr_path G (take_prfx i) v v''.

End TmprStgy.

(** * Theorem 2: Strategy Exists%\index{Theorem 2: Strategy Exists}% *)

Section StgyExists.

  (** For the data flow semantics, [tmpr_path] is equivalent to
      [io_path] and [tmpr']. *)

  Lemma phrase_to_flow_tmpr_path : forall t p ps e pi v v',
      tmpr_path (phrase_to_flow t p ps e) pi v v' <->
        io_path (phrase_to_flow t p ps e) pi /\ tmpr' pi v v'.
  Proof.
    unfold tmpr_path, tmpr; intuition.
    apply phrase_to_flow_accm_graph; auto.
  Qed.

  (** Any path of length 2 through the data flow semantics is local. *)

  Lemma phrase_to_flow_edge_local :
    forall t p ps e (v v' : io_evt (phrase_to_flow t p ps e)),
      In (v, v') (io_to_graph (phrase_to_flow t p ps e)) ->
      is_local [v; v'].
  Proof.
    intros; unfold is_local.
    apply (phrase_to_flow_edge_plc_adj t p ps e v v') in H.
    exists (recvp (io_evt_lbl v)).
    unfold local; intros.
    split; intros; try (simpl in *; lia).
    destruct H0.
    - right. rewrite nth_safe_fst; auto.
    - left. rewrite H.
      rewrite (to_idx_nat_evi i).
      destruct i as [n Hn];
        simpl idx_evi; simpl in H0; subst.
      f_equal.
  Qed.

  (** Excluding the output event, every measurement event in the data
      flow semantics has a tamper strategy. *)

  Theorem stgy_exists :
    forall t p ps e (v : io_evt (phrase_to_flow t p ps e)),
      meas_lbl (io_evt_lbl v) ->
      v <> io_output_evt (phrase_to_flow t p ps e) ->
      exists V, tmpr_stgy (phrase_to_flow t p ps e) v V.
  Proof.
    intros.
    pose proof (
        phrase_to_flow_meas_out_edge t p ps e v H
      ).
    destruct H1 as [H1|[v' H1]]; try contradiction.
    (* The other event in v's unique outgoing edge *)
    exists [v'].
    unfold tmpr_stgy; intros.
    pose proof (
        length_fst_lst_neq H3 H4 H0
      ).
    exists v', (to_idx H5).
    split; try (simpl; auto).
    pose proof (
        io_path_uniq_edge_out H5 H2 H3 H1
      ).
    split; auto.
    rewrite phrase_to_flow_tmpr_path. split.
    - apply (io_path_prfx H2); auto.
      apply take_prfx_is_prfx.
    - destruct H3 as [i [H3 H3']].
      rewrite (to_idx_nat_evi i) in *.
      destruct i as [n Hn].
      simpl in H3, H3'. subst n.
      pose proof (
          take_two pi v v' Hn H5 H3' H6
        ).
      rewrite H3. destruct H1.
      apply local_path_tmprs; auto.
      + assert (0 < length [v; v']) by (simpl; lia).
        exists (to_idx H8); auto.
      + assert (length [v; v'] - 1 < length [v; v'])
          by (simpl; lia).
        exists (to_idx H8); auto.
      + eapply io_acyclic_edge_neq; eauto.
        apply phrase_to_flow_acyclic.
      + apply phrase_to_flow_edge_local; auto.
  Qed.

End StgyExists.

Unset Implicit Arguments.
