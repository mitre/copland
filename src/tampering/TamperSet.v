(** Tamper sets are sets of places that can tamper along paths from
    measurement events. *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import Lia List.
Import ListNotations.

Require Import AllSet Copland DataFlow Graph Index Label
  Path Preamble Prefix Tamper.

Set Implicit Arguments.

Definition plcs := aset plc.

(** The set of all [plc] *)

Definition plcs_all : plcs := All plc.

(** The empty set of [plc] *)

Definition plcs_empty : plcs := ASet [].

(** Inject a [plc] into a singleton [plcs]. *)

Definition plcs_sngl (p : plc) : plcs := aset_sngl p.

Definition plcs_mem   :=   aset_mem String.string_dec.
Definition plcs_inter := aset_inter String.string_dec.
Definition plcs_union := aset_union String.string_dec.

Ltac plc_eq s := destruct (String.string_dec s s); try contradiction.

(** * Definition 11: Tamper set%\index{Definition 11: Tamper set}% *)

Section TmprSet.

  Variable L : lbls.

  (** Compute the set of places at the end of a path that can tamper
      with evidence created at the start of the path

      Note that [pi] is assumed to be a [rev_path], i.e., the last
      event is at the head of the list *)

  Fixpoint tmpr_set (pi : evt_seq L) : plcs :=
    match pi with
    | [] => plcs_all
    | [v] =>
        if meas_lblb (nth_safe L v) then
          plcs_all
        else
          plcs_empty
    | v :: pi' =>
        if sig_lblb (nth_safe L v) then
          plcs_inter (plcs_sngl (sendp (nth_safe L v))) (tmpr_set pi')
        else
          tmpr_set pi'
    end.

  (** The next three lemmas serve as rewrite rules for the [tmpr_set]
      logic. *)

  (** Tamper set for a singleton measurement event *)

  Lemma tmpr_set_sngl_meas : forall v,
      meas_lblb (nth_safe L v) = true -> tmpr_set [v] = plcs_all.
  Proof.
    simpl; intros; rewrite H; reflexivity.
  Qed.

  (** Tamper set for a non-singleton path ending in a signing event *)

  Lemma tmpr_set_sign : forall pi v v',
      sig_lblb (nth_safe L v) = true ->
      tmpr_set (v :: v' :: pi) =
        plcs_inter (plcs_sngl (sendp (nth_safe L v))) (tmpr_set (v' :: pi)).
  Proof.
    simpl; intros; rewrite H; reflexivity.
  Qed.

  (** Tamper set for a non-singleton path ending in a non-signing
      event *)

  Lemma tmpr_set_non_sign : forall pi v v',
      sig_lblb (nth_safe L v) = false ->
      tmpr_set (v :: v' :: pi) = tmpr_set (v' :: pi).
  Proof.
    simpl; intros; rewrite H; reflexivity.
  Qed.

  (** Lengthening an event sequence by a single event is weakly
      decreasing. *)

  Lemma tmpr_set_weakly_decreasing_step :
    forall pi v p,
      plcs_mem p (tmpr_set (v :: pi)) = true ->
      plcs_mem p (tmpr_set pi) = true.
  Proof.
    destruct pi; intros; auto.
    destruct (sig_lblb (nth_safe L v)) eqn:H'.
    - rewrite tmpr_set_sign in H; auto.
      apply aset_inter_mem in H as [_ H].
      assumption.
    - rewrite tmpr_set_non_sign in H; auto.
  Qed.

  (** Lengthening an event sequence arbitrarily is weakly decreasing. *)

  Lemma tmpr_set_weakly_decreasing :
    forall pi pi' p,
      plcs_mem p (tmpr_set (pi' ++ pi)) = true ->
      plcs_mem p (tmpr_set pi) = true.
  Proof.
    induction pi'; auto. destruct pi'.
    - apply tmpr_set_weakly_decreasing_step.
    - intros. apply IHpi'.
      apply (tmpr_set_weakly_decreasing_step _ _ _ H).
  Qed.

  (** If a lengthened event sequence's tamper set is [plcs_all], the
      original sequence's tamper set is also [plcs_all]. *)

  Lemma tmpr_set_plcs_all_cons :
    forall pi v,
      tmpr_set (v :: pi) = plcs_all ->
      tmpr_set pi = plcs_all.
  Proof.
    destruct pi; intros; auto.
    destruct (sig_lblb (nth_safe L v)) eqn:H'.
    - rewrite tmpr_set_sign in H; auto.
      apply aset_inter_all in H as [H _].
      discriminate.
    - rewrite tmpr_set_non_sign in H; auto.
  Qed.

  (** A tamper set is either the set of all places, the empty set or a
      singleton. *)

  Lemma tmpr_set_trichotomy :
    forall pi,
      tmpr_set pi = plcs_all
      \/ tmpr_set pi = plcs_empty
      \/ exists p, tmpr_set pi = plcs_sngl p.
  Proof.
    induction pi; auto. destruct pi.
    - simpl in IHpi; destruct IHpi as [H|[H|H']];
        try destruct H' as [p H]; try discriminate.
      (* Singleton, either all places or empty *)
      destruct (meas_lblb (nth_safe L a)) eqn:H';
        [left | right; left]; simpl; rewrite H'; auto.
    - (* Take cases on whether a is signing event *)
      destruct (sig_lblb (nth_safe L a)) eqn:H'.
      + (* Signing event *)
        right. repeat rewrite tmpr_set_sign; auto.
        apply sig_lbl_reflect in H' as H''.
        destruct H'' as [p [e H'']].
        destruct IHpi as [IH|[IH|[p' IH]]]; rewrite IH.
        * (* Singleton *)
          right. exists p; rewrite H''; auto.
        * (* Empty *)
          left; auto.
        * rewrite H''; simpl.
          destruct (String.string_dec p p'); subst.
          -- right; eexists. reflexivity.
          -- left; auto.
      + (* Non-signing event *)
        repeat rewrite tmpr_set_non_sign; auto.
  Qed.

  (** An event sequence ending in a measurement event is [p]-signing
      iff its tamper set is the set of all places or just [{p}]. *)

  Lemma p_signing_iff_tmpr_set :
    forall p pi,
      meas_lst pi ->
      p_signing p pi <-> tmpr_set pi = plcs_all \/ tmpr_set pi = plcs_sngl p.
  Proof.
    intros; rewrite p_signing_iff_p_signing'.
    split; intros.
    - induction H0; auto.
      + apply sig_lbl_reflect in H1 as H1'.
        destruct H1 as [p' [e H1]].
        rewrite H1 in H2; simpl in H2; subst p'.
        destruct pi.
        * apply meas_lst_sngl in H.
          apply sig_lbl_reflect in H1'.
          apply sig_lbl_neq_meas_lbl in H1'.
          contradiction.
        * right.
          apply meas_lst_cons_iff in H.
          apply IHp_signing' in H.
          repeat rewrite tmpr_set_sign; auto.
          repeat rewrite H1; simpl sendp.
          destruct H; repeat rewrite H; simpl; auto.
          destruct (String.string_dec p p);
            try contradiction; auto.
      + rewrite sig_lbl_reflect in H1.
        apply Bool.not_true_iff_false in H1.
        destruct pi.
        * left.
          apply meas_lst_sngl in H.
          apply meas_lbl_reflect in H.
          rewrite tmpr_set_sngl_meas; auto.
        * apply meas_lst_cons_iff  in H.
          apply IHp_signing' in H.
          repeat rewrite tmpr_set_non_sign; auto.
    - induction pi; try apply ps_base.
      destruct pi.
      + apply meas_lst_sngl in H.
        apply meas_lbl_neq_sig_lbl in H.
        apply ps_rest; try constructor; auto.
      + apply meas_lst_cons_iff in H.
        destruct (sig_lblb (nth_safe L a)) eqn:H'.
        * apply sig_lbl_reflect in H' as H''.
          rewrite tmpr_set_sign in H0; auto.
          destruct H0.
          -- apply aset_inter_all in H0 as [H0 _].
             discriminate.
          -- apply aset_inter_sngls_lft in H0 as H0'.
             apply ps_sign; auto.
             apply IHpi; auto.
             pose proof (tmpr_set_trichotomy (i :: pi)).
             destruct H1 as [H1|[H1|[p' H1]]];
               rewrite H1 in H0; try discriminate; auto.
             rewrite H0' in H0; simpl in H0.
             destruct (String.string_dec p p');
               subst; try discriminate; auto.
        * rewrite tmpr_set_non_sign in H0; auto.
          apply Bool.not_true_iff_false in H'.
          rewrite <- sig_lbl_reflect in H'.
          apply ps_rest; auto.
  Qed.

End TmprSet.

(** * Theorem 1%\index{Theorem 1}% *)

Section Thm16.

  (** Shows that [tmpr_set] can be used to verify whether a path
      permits tamper. *)

  Theorem rev_tmpr'_iff_ts_inter_ne :
    forall (L : lbls) (pi : evt_seq L) v v',
      lst_elem pi v ->
      meas_lbl (nth_safe L v) ->
      acyclic_evt_seq (v' :: pi) ->
      rev_tmpr' (v' :: pi) v' v <->
        plcs_inter
          (tmpr_set pi)
          (ASet [sendp (nth_safe L v'); recvp (nth_safe L v')]) <> plcs_empty.
  Proof.
    intros L pi v v' H0 H0' H0''.
    assert (meas_lst pi) by (exists v; auto).
    split.
    - unfold rev_tmpr';
        intros [H1 [H2 [H3 [H4 H5]]]]; intro.
      assert (meas_lst (v' :: pi)) by (exists v; auto).
      (* A p-signing event seq has singleton or [plcs_all] tamper set *)
      destruct H5; apply p_signing_iff_tmpr_set in H5; auto; destruct H5;
        (* Handles the two [tmpr_set pi = plcs_all] cases *)
        try (
            apply tmpr_set_plcs_all_cons in H5;
            rewrite H5 in H6; simpl in H6;
            discriminate
          ).
      (* For singleton cases, same proof from weakly decreasing *)
      + (* tmpr_set pi contains sendp (nth_safe L v') *)
        pose proof (
            tmpr_set_weakly_decreasing_step pi v' (sendp (nth_safe L v'))
          ).
        rewrite H5 in H8. simpl in H8.
        plc_eq (sendp (nth_safe L v')); intuition.
        assert (
            plcs_mem
              (sendp (nth_safe L v'))
              (ASet [sendp (nth_safe L v'); recvp (nth_safe L v')])
            = true
          ) by (simpl; plc_eq (sendp (nth_safe L v')); auto).
        pose proof (conj H9 H8).
        apply aset_inter_mem in H10.
        apply aset_mem_nonempty in H10.
        contradiction.
      + (* tmpr_set pi contains recvp (nth_safe L v') *)
        pose proof (
            tmpr_set_weakly_decreasing_step pi v' (recvp (nth_safe L v'))
          ).
        rewrite H5 in H8. simpl in H8.
        plc_eq (recvp (nth_safe L v')); intuition.
        assert (
            plcs_mem
              (recvp (nth_safe L v'))
              (ASet [sendp (nth_safe L v'); recvp (nth_safe L v')])
            = true
          ). {
          apply aset_mem_cons.
          simpl; plc_eq (recvp (nth_safe L v')); auto.
        }
        pose proof (conj H9 H8).
        apply aset_inter_mem in H10.
        apply aset_mem_nonempty in H10.
        contradiction.
    - (* Check all [rev_tmpr'] conditions hold *)
      intros; unfold rev_tmpr'.
      assert (lst_elem (v' :: pi) v) by (apply lst_elem_cons; auto).
      assert (fst_elem (v' :: pi) v') by apply fst_elem_cons.
      repeat split; auto.
      + apply not_eq_sym.
        apply (acyclic_evt_seq_fst_neq_lst H0''); auto.
        destruct pi; try (simpl; lia).
        destruct H0 as [[n Hn] _]; simpl in *; lia.
      + (* Take cases on the [tmpr_set_trichotomy] possibilities *)
        repeat rewrite p_signing_iff_p_signing'.
        pose proof (tmpr_set_trichotomy pi).
        destruct (sig_lblb (nth_safe L v')) eqn:H'.
        * (* v' is a signature event *)
          apply sig_lbl_reflect in H'.
          destruct H4 as [H4|[H4|[p H4]]];
            rewrite H4 in H1;
            try (simpl in H1; contradiction).
          -- left. apply ps_sign; auto.
             rewrite <- p_signing_iff_p_signing'.
             apply p_signing_iff_tmpr_set; auto.
          -- apply aset_inter_sngl_nonempty_lft in H1.
             simpl in H1.
             destruct (
                 String.string_dec p (sendp (nth_safe L v'))
               ); subst.
             ++ left. apply ps_sign; auto.
                rewrite <- p_signing_iff_p_signing'.
                apply p_signing_iff_tmpr_set; auto.
             ++ destruct (
                    String.string_dec p (recvp (nth_safe L v'))
                  ); subst; try discriminate.
                right. apply ps_sign;
                  try apply sig_lbl_sendp_eq_recvp; auto.
                rewrite <- p_signing_iff_p_signing'.
                apply p_signing_iff_tmpr_set; auto.
        * (* v' is not a signature event *)
          apply Bool.not_true_iff_false in H'.
          rewrite <- sig_lbl_reflect in H'.
          destruct H4 as [H4|[H4|[p H4]]];
            rewrite H4 in H1;
            try (simpl in H1; contradiction).
          -- left. apply ps_rest; auto.
             rewrite <- p_signing_iff_p_signing'.
             apply p_signing_iff_tmpr_set; auto.
          -- apply aset_inter_sngl_nonempty_lft in H1.
             simpl in H1.
             destruct (
                 String.string_dec p (sendp (nth_safe L v'))
               ); subst.
             ++ left. apply ps_rest; auto.
                rewrite <- p_signing_iff_p_signing'.
                apply p_signing_iff_tmpr_set; auto.
             ++ destruct (
                    String.string_dec p (recvp (nth_safe L v'))
                  ); subst; try discriminate.
                right. apply ps_rest; auto.
                rewrite <- p_signing_iff_p_signing'.
                apply p_signing_iff_tmpr_set; auto.
  Qed.

End Thm16.

(** * Definition 13: Protected paths%\index{Definition 13: Protected paths}% *)

Section Protected.

  Variable L : lbls.

  (** These definitions of protected and protected graph differ
      slightly from the paper's in that they only constrain paths
      starting with measurement events according to Condition 2 of
      Definition 13. *)

  Definition protected (pi : evt_seq L) : Prop :=
    meas_fst pi
    /\ (forall (i : idx pi),
           xplc_comm_lbl (nth_safe L (nth_safe pi i)) ->
           (forall (p : plc),
               plcs_mem p (tmpr_set (rev (take_prfx i))) = true ->
               plcs_mem p (plcs_sngl (sendp (nth_safe L (nth_safe pi i)))) = true)).

  Definition protected_graph (G : io_graph L) : Prop :=
    forall pi,
      io_path G pi -> meas_fst pi -> protected pi.

  (** The [prot] property is an equivalent, inductive alternative to
      [protected] that is intended for use with reverse paths, making
      it simpler to reason about.  We prove equivalence below. *)

  Inductive prot : evt_seq L -> Prop :=
  | prot_base :
    forall v, meas_lbl (nth_safe L v) -> prot [v]
  | prot_xplc :
    forall pi v,
      prot pi ->
      xplc_comm_lbl (nth_safe L v) ->
      (forall p,
          plcs_mem p (tmpr_set pi) = true ->
          plcs_mem p (plcs_sngl (sendp (nth_safe L v))) = true) ->
      prot (v :: pi)
  | prot_rest :
    forall pi v,
      prot pi -> ~(xplc_comm_lbl (nth_safe L v)) -> prot (v :: pi).

  (** The analogue of [protected_graph] for the [prot] property *)

  Definition prot_graph (G : io_graph L) : Prop :=
    forall pi, io_rev_path G pi -> meas_lst pi -> prot pi.

  (** An event sequence is [protected] iff its reverse is [prot]. *)

  Lemma protected_iff_rev_prot :
    forall pi, protected pi <-> prot (rev pi).
  Proof.
    unfold protected. split.
    - pattern pi. apply rev_ind; intros.
      + destruct H. apply meas_fst_non_nil in H. contradiction.
      + rewrite rev_unit. intuition.
        destruct (rev l) eqn:Hrl.
        * apply nil_iff_rev_nil in Hrl. subst; simpl app in *.
          apply meas_fst_sngl in H1.
          constructor; auto.
        * assert (l = rev l0 ++ [i])
            by (rewrite <- (rev_involutive l); rewrite Hrl; auto).
          subst l. apply meas_fst_app_iff in H1 as H1'.
          destruct (xplc_comm_lblb (nth_safe L x)) eqn:H'.
          -- apply xplc_comm_lbl_reflect in H'.
             apply prot_xplc; auto.
             ++ apply H0; auto. intros.
                assert (
                    xplc_comm_lbl
                      (nth_safe L (nth_safe ((rev l0 ++ [i]) ++ [x]) (app_lft [x] i0)))
                  ) by (rewrite app_lft_nth_safe; auto).
                pose proof (H2 _ H4).
                rewrite app_lft_nth_safe in H5. apply H5.
                rewrite (to_idx_nat_evi i0) in *.
                destruct i0 as [n Hn]; simpl idx_evi in *.
                erewrite prfx_lft; eauto.
             ++ intros. rewrite <- Hrl in H.
                assert (
                    length ((rev l0) ++ [i]) < length ((rev l0 ++ [i]) ++ [x])
                  ) by (repeat rewrite app_length; simpl; lia).
                assert (
                    nth_safe ((rev l0 ++ [i]) ++ [x]) (to_idx H3) = x
                  ). {
                  assert (
                      length ((rev l0) ++ [i]) <= idx_nat (to_idx H3)
                    ) by (simpl; lia).
                  assert (
                      (idx_nat (to_idx H3)) - (length ((rev l0) ++ [i])) < length [x]
                    ) by (simpl; lia).
                  rewrite (nth_safe_app_rht _ _ _ H4 H5).
                  apply nth_safe_sngl.
                }
                assert (
                    xplc_comm_lbl (nth_safe L (nth_safe ((rev l0 ++ [i]) ++ [x]) (to_idx H3)))
                  ) by (rewrite H4; auto).
                assert (
                    idx_nat (to_idx H3) = length ((rev l0 ++ [i]) ++ [x]) - 1
                  ) by (simpl; repeat rewrite app_length; simpl; lia).
                pose proof (H2 _ H5). rewrite H4 in H7. apply H7.
                rewrite take_prfx_all; auto.
                rewrite rev_unit. simpl. rewrite rev_unit.
                assert (sig_lblb (nth_safe L x) = false). {
                  apply xplc_comm_is_comm in H'.
                  destruct H' as [[q [q' [e H']]]|[q [q' [e H']]]];
                    rewrite H'; reflexivity.
                }
                rewrite H8. rewrite rev_unit in H. auto.
          -- apply Bool.not_true_iff_false in H'.
             rewrite <- xplc_comm_lbl_reflect in H'.
             apply prot_rest; auto.
             apply H0; auto. intros.
             assert (
                 xplc_comm_lbl
                   (nth_safe L (nth_safe ((rev l0 ++ [i]) ++ [x]) (app_lft [x] i0)))
               ) by (rewrite app_lft_nth_safe; auto).
             pose proof (H2 _ H4).
             rewrite app_lft_nth_safe in H5. apply H5.
             rewrite (to_idx_nat_evi i0) in *.
             destruct i0 as [n Hn]; simpl idx_evi in *.
             erewrite prfx_lft; eauto.
    - intro.
      replace pi with (rev (rev pi)); try apply rev_involutive.
      induction H; intros.
      + split.
        * simpl. exists v. intuition.
          assert (0 < length [v]) by (simpl; lia).
          exists (to_idx H0); auto.
        * simpl rev. intros.
          unfold xplc_comm_lbl in H0.
          rewrite nth_safe_sngl in H0.
          destruct H as [p' [msr [q [tgt [ps [e H]]]]]].
          rewrite H in H0. contradiction.
      + destruct IHprot as [IH0 IH1]. split.
        * apply meas_fst_rev_cons; auto.
        * intros.
          assert (
              idx_nat i < length (rev pi0) + length [v]
            ). {
            clear H2 H3; simpl in i.
            destruct i; simpl.
            rewrite app_length in l; auto.
          }
          assert (
              idx_nat i < length (rev pi0) \/ idx_nat i = length (rev pi0)
            ) by (simpl in *; lia).
          destruct H5.
          -- simpl rev in *.
             rewrite nth_safe_app_lft with (Hn' := H5) in *.
             pose proof (IH1 _ H2). apply H6.
             rewrite <- prfx_lft; auto.
          -- assert (idx_nat i = length (rev (v :: pi0)) - 1).
             { rewrite H5; simpl. rewrite app_length. simpl; lia. }
             rewrite take_prfx_all in H3; auto.
             rewrite rev_involutive in H3.
             assert (length (rev pi0) <= idx_nat i) by lia.
             pose proof (nat_sub_lt _ _ _ H4 H7). simpl rev.
             rewrite (nth_safe_app_rht _ _ _ H7 H8).
             rewrite nth_safe_sngl. apply H1.
             eapply tmpr_set_weakly_decreasing_step. eauto.
      + destruct IHprot as [IH0 IH1]. split.
        * apply meas_fst_rev_cons; auto.
        * simpl rev. intros.
          assert (idx_nat i < length (rev pi0) + length [v]).
          { clear H1 H2. destruct i; simpl. rewrite app_length in l. auto. }
          assert (idx_nat i < length (rev pi0) \/ length (rev pi0) <= idx_nat i) by lia.
          destruct H4.
          -- rewrite nth_safe_app_lft with (Hn' := H4) in *.
             pose proof (IH1 _ H1). apply H5.
             rewrite <- prfx_lft; auto.
          -- pose proof (nat_sub_lt _ _ _ H3 H4).
             rewrite (nth_safe_app_rht _ _ _ H4 H5) in H1.
             rewrite nth_safe_sngl in H1. contradiction.
  Qed.

  (** An IO graph is a protected graph iff it is a [prot] graph. *)

  Lemma protected_graph_iff_prot_graph :
    forall G, protected_graph G <-> prot_graph G.
  Proof.
    unfold protected_graph, prot_graph.
    split; intros.
    - replace pi with (rev (rev pi)) in *;
        try apply rev_involutive.
      apply io_path_iff_rev_path_rev in H0.
      apply meas_fst_iff_meas_lst_rev in H1.
      pose proof (H _ H0 H1).
      apply protected_iff_rev_prot; auto.
    - apply io_path_iff_rev_path_rev in H0.
      apply meas_fst_iff_meas_lst_rev in H1.
      pose proof (H _ H0 H1).
      apply protected_iff_rev_prot; auto.
  Qed.

  (** The tamper set of a protected sequence is a subset of [{sendp
      v}] for every cross-place communication event [v] it contains. *)

  Lemma prot_xplc_comm_tmpr_set :
    forall pi i,
      prot pi ->
      xplc_comm_lbl (nth_safe L (nth_safe pi i)) ->
      (forall p,
          plcs_mem p (tmpr_set pi) = true ->
          plcs_mem p (plcs_sngl (sendp (nth_safe L (nth_safe pi i)))) = true).
  Proof.
    intros pi i H. revert i.
    induction H; intros.
    - rewrite nth_safe_sngl in H0.
      apply meas_lbl_sendp_eq_recvp in H.
      contradiction.
    - rewrite (to_idx_nat_evi i) in *.
      destruct i as [n Hn]; simpl idx_evi in *.
      destruct n.
      + clear H2. simpl nth_safe.
        apply (tmpr_set_weakly_decreasing_step pi v) in H3. auto.
      + assert (Hn' : n < length pi) by (simpl in *; lia).
        assert (
            xplc_comm_lbl (nth_safe L (nth_safe pi (to_idx Hn')))
          ) by (rewrite <- (nth_safe_cons Hn); auto).
        apply (tmpr_set_weakly_decreasing_step pi v) in H3.
        pose proof (IHprot _ H4 p H3).
        rewrite <- (nth_safe_cons Hn) in H5. auto.
    - rewrite (to_idx_nat_evi i) in *.
      destruct i as [n Hn]; simpl idx_evi in *.
      destruct n; try (simpl in H1; contradiction).
      assert (Hn' : n < length pi) by (simpl in *; lia).
      assert (
          xplc_comm_lbl (nth_safe L (nth_safe pi (to_idx Hn')))
        ) by (rewrite <- (nth_safe_cons Hn); auto).
      apply (tmpr_set_weakly_decreasing_step pi v) in H2.
      pose proof (IHprot _ H3 p H2).
      rewrite <- (nth_safe_cons Hn) in H4. auto.
  Qed.

End Protected.

(** * Theorem 3%\index{Theorem 3}% *)

Section Thm21.

  Variable L : lbls.

  (** Under a no-teleportation assumption, a protected,
      tamper-permitting event sequence may only have an initial
      cross-place communication event. *)

  Lemma prot_tmpr_xplc_comm_evt :
    forall (pi : evt_seq L) v v',
      rev_no_teleport pi ->
      prot pi ->
      rev_tmpr' pi v' v ->
      forall i,
        xplc_comm_lbl (nth_safe L (nth_safe pi i)) ->
        idx_nat i = 0.
  Proof.
    (* i indexes a xplc_comm_lbl event in pi *)
    intros. rewrite (to_idx_nat_evi i) in *.
    destruct i as [n Hn]; simpl idx_evi in *; simpl.
    (* Take cases on the constructors of [prot] *)
    inv H0; try (simpl in *; lia).
    - (* First event is xplc_comm_lbl *)
      destruct n; auto.
      destruct H1 as [H' [H0 [H0' [H1 H1']]]].
      assert (meas_lst (v0 :: pi0)) by (eexists; eauto).
      apply fst_elem_cons' in H0; subst.
      pose proof (tmpr_set_weakly_decreasing_step pi0 v') as H7.
      assert (
          H8 :
          forall p,
            plcs_mem p (tmpr_set (v' :: pi0)) = true ->
            plcs_mem p (plcs_sngl (sendp (nth_safe L v'))) = true
        ) by auto.
      (* Take cases on (sendp v')-signing or (recvp v')-signing.
         This will imply that the tmpr_set of the sequence is all
         places or respectively {sendp v'} or {recvp v'} *)
      destruct H1'.
      + (* (sendp v')-signing *)
        apply p_signing_iff_tmpr_set in H0; auto.
        destruct H0 as [H0|H0]; rewrite H0 in H8.
        * (* Tamper set is all places *)
          specialize H8 with (recvp (nth_safe L v')).
          simpl in H8; intuition.
          destruct (
              String.string_dec
                (recvp (nth_safe L v'))
                (sendp (nth_safe L v'))
            ); try discriminate.
          (* Leads to the contradiction that v' is not a xplc_comm event *)
          symmetry in e. contradiction.
        * (* Tamper set is {sendp v'} *)
          clear H8. rewrite H0 in *.
          assert (Hn' : n < length pi0) by (simpl in *; lia).
          rewrite (nth_safe_cons _ Hn') in H2.
          pose proof (prot_xplc_comm_tmpr_set (to_idx Hn') H3 H2).
          (* Implies that {sendp v'} is a subset of {sendp pi0[n]} *)
          assert (
              forall p,
                plcs_mem p (plcs_sngl (sendp (nth_safe L v'))) = true ->
                plcs_mem p (plcs_sngl (sendp (nth_safe L (nth_safe pi0 (to_idx Hn'))))) = true
            ) by intuition.
          specialize H9 with (sendp (nth_safe L v')) as H9'.
          simpl in H9'; plc_eq (sendp (nth_safe L v')); intuition.
          (* Which implies sendp v' = sendp pi0[n] *)
          destruct (
              String.string_dec
                (sendp (nth_safe L v'))
                (sendp (nth_safe L (nth_safe pi0 (to_idx Hn'))))
            ); try discriminate; clear H10.
          (* Which implies sendp v' <> recvp pi0[n], since the latter is xplc_comm *)
          assert (
              sendp (nth_safe L v') <> recvp (nth_safe L (nth_safe pi0 (to_idx Hn')))
            ). { intro. rewrite H10 in e0. symmetry in e0; contradiction. }
          (* But this implies a xplc_comm event v'' (indexed by k)
             separates v' from pi0[n] and the sending place of v'' is
             the receiving place at pi0[n] *)
          clear e0. assert (0 < length (v' :: pi0)) by (simpl; lia).
          assert (v' = nth_safe (v' :: pi0) (to_idx H11)) by auto.
          assert (idx_nat (to_idx H11) < idx_nat (to_idx Hn)) by (simpl; lia).
          rewrite H12 in H10. rewrite <- (nth_safe_cons Hn) in H8, H10.
          pose proof (rev_xplc_comm_between _ _ _ H H13 H10).
          destruct H14 as [k [H14 [H15 H16]]].
          rewrite (to_idx_nat_evi k) in *.
          destruct k as [m Hm]; simpl idx_evi in *; simpl in H14.
          destruct m; try lia; clear H14.
          assert (Hm' : m < length pi0) by (simpl in *; lia).
          rewrite nth_safe_cons with (Hn := Hm') in H15, H16.
          rewrite nth_safe_cons with (Hn := Hn') in H8, H16.
          pose proof (prot_xplc_comm_tmpr_set (to_idx Hm') H3 H15).
          (* But then {sendp v'} must also be a subset of {sendp v''} *)
          assert (
              forall p,
                plcs_mem p (plcs_sngl (sendp (nth_safe L v'))) = true ->
                plcs_mem p (plcs_sngl (sendp (nth_safe L (nth_safe pi0 (to_idx Hm'))))) = true
            ) by intuition.
          (* Which in turn implies sendp v' = sendp v'' = recvp pi0[n], a contradiction *)
          rewrite H16 in H17.
          specialize H9 with (sendp (nth_safe L v')).
          specialize H17 with (sendp (nth_safe L v')).
          simpl in H9, H17. plc_eq (sendp (nth_safe L v')); intuition.
          destruct (
              String.string_dec
                (sendp (nth_safe L v'))
                (sendp (nth_safe L (nth_safe pi0 (to_idx Hn'))))
            ); try discriminate.
          destruct (
              String.string_dec
                (sendp (nth_safe L v'))
                (recvp (nth_safe L (nth_safe pi0 (to_idx Hn'))))
            ); try discriminate.
          rewrite e1 in e2. contradiction.
      + (* (recvp v')-signing *)
        apply p_signing_iff_tmpr_set in H0; auto.
        (* This leads to a contradiction: recvp v' is always in the
           tamper set but cannot be in {sendp v'} since v' is xplc_comm *)
        destruct H0 as [H0|H0]; rewrite H0 in H8;
          specialize H8 with (recvp (nth_safe L v'));
          simpl in H8; intuition;
          destruct (String.string_dec (recvp (nth_safe L v')) (sendp (nth_safe L v')));
          try discriminate; try (symmetry in e; contradiction).
        plc_eq (recvp (nth_safe L v')). intuition. discriminate.
    - (* First event is non-xplc_comm_lbl, very similar to previous case *)
      destruct n; try (simpl in *; contradiction).
      destruct H1 as [H' [H0 [H0' [H1 H1']]]].
      assert (meas_lst (v0 :: pi0)) by (eexists; eauto).
      apply fst_elem_cons' in H0; subst.
      pose proof (tmpr_set_weakly_decreasing_step pi0 v').
      apply not_xplc_comm_lbl in H4. rewrite <- H4 in H1'.
      assert (p_signing (sendp (nth_safe L v')) (v' :: pi0)) by intuition; clear H1'.
      apply p_signing_iff_tmpr_set in H6; auto.
      assert (Hn' : n < length pi0) by (simpl in *; lia).
      rewrite (nth_safe_cons _ Hn') in H2.
      pose proof (prot_xplc_comm_tmpr_set (to_idx Hn') H3 H2).
      assert (
          forall p,
            plcs_mem p (tmpr_set (v' :: pi0)) = true ->
            plcs_mem p (plcs_sngl (sendp (nth_safe L (nth_safe pi0 (to_idx Hn'))))) = true
        ) by intuition.
      destruct H6 as [H6|H6]; rewrite H6 in H8.
      + pose proof (
            plc_exists_neq (sendp (nth_safe L (nth_safe pi0 (to_idx Hn'))))
          ) as [q Hq].
        specialize H8 with q; simpl in H8. intuition.
        destruct (
            String.string_dec q (sendp (nth_safe L (nth_safe pi0 (to_idx Hn'))))
          ); try contradiction; discriminate.
      + destruct (
            String.string_dec
              (sendp (nth_safe L v'))
              (sendp (nth_safe L (nth_safe pi0 (to_idx Hn'))))
          ) as [Hp|Hp] eqn:Hdec.
        * clear Hdec.
          assert (
              sendp (nth_safe L v') <> recvp (nth_safe L (nth_safe pi0 (to_idx Hn')))
            ). { intro. rewrite H9 in Hp. symmetry in Hp. contradiction. }
          clear Hp. assert (0 < length (v' :: pi0)) by (simpl; lia).
          assert (v' = nth_safe (v' :: pi0) (to_idx H10)) by auto.
          rewrite H11 in H9; rewrite <- (nth_safe_cons Hn) in H7, H9.
          assert (idx_nat (to_idx H10) < idx_nat (to_idx Hn)) by (simpl; lia).
          pose proof (rev_xplc_comm_between _ _ _ H H12 H9).
          destruct H13 as [k [H13 [H14 H15]]].
          rewrite (to_idx_nat_evi k) in *.
          destruct k as [m Hm]; simpl idx_evi in *; simpl in H13.
          destruct m; try lia; clear H13.
          assert (Hm' : m < length pi0) by (simpl in *; lia).
          rewrite nth_safe_cons with (Hn := Hm') in H14, H15.
          rewrite nth_safe_cons with (Hn := Hn') in H7, H15.
          pose proof (prot_xplc_comm_tmpr_set (to_idx Hm') H3 H14).
          assert (
              forall p,
                plcs_mem p (tmpr_set (v' :: pi0)) = true ->
                plcs_mem p (plcs_sngl (sendp (nth_safe L (nth_safe pi0 (to_idx Hm'))))) = true
            ) by intuition.
          rewrite H6 in H16. rewrite H15 in H16.
          specialize H8 with (sendp (nth_safe L v')).
          specialize H16 with (sendp (nth_safe L v')).
          simpl in H8, H16. plc_eq (sendp (nth_safe L v')); intuition.
          destruct (
              String.string_dec
                (sendp (nth_safe L v'))
                (sendp (nth_safe L (nth_safe pi0 (to_idx Hn'))))
            ); try discriminate.
          destruct (
              String.string_dec
                (sendp (nth_safe L v'))
                (recvp (nth_safe L (nth_safe pi0 (to_idx Hn'))))
            ); try discriminate.
          rewrite e0 in e1. contradiction.
        * specialize H8 with (sendp (nth_safe L v')).
          simpl in H8. plc_eq (sendp (nth_safe L v')).
          rewrite Hdec in H8. intuition. discriminate.
  Qed.

  (** Under a no-teleportation assumption, a protected,
      tamper-permitting event sequence is local to the sending place
      of its terminal measurement event. *)

  Theorem prot_tmpr_is_local :
    forall (pi : evt_seq L) v v',
      rev_no_teleport pi ->
      prot pi ->
      rev_tmpr' pi v' v ->
      local (sendp (nth_safe L v)) pi.
  Proof.
    (* This sequence can only have an initial xplc_comm_lbl by
       [prot_tmpr_xplc_comm_evt] *)
    intros.
    (* So it can only have an initial or terminal one *)
    assert (
        forall i,
          xplc_comm_lbl (nth_safe L (nth_safe pi i)) ->
          idx_nat i = 0 \/ idx_nat i = length pi - 1
      ). {
      intros. left.
      eapply prot_tmpr_xplc_comm_evt; eauto.
    }
    (* But any such sequence is local to some place *)
    apply is_local_xplc_comm_evt in H2; auto.
    (* Deduce what place it is from the meas_lbl *)
    destruct H1 as [H1 [_ [H1' _]]].
    destruct H2 as [p H2].
    apply (local_lst_plcs H2) in H1.
    apply meas_lbl_sendp_eq_recvp in H1'.
    rewrite <- H1' in H1.
    destruct H1; subst; auto.
  Qed.

End Thm21.

Unset Implicit Arguments.
