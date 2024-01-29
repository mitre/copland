(** Data flow graphs *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import Lia List.
Import ListNotations.

Require Import Copland Evidence Graph Index Label Path Preamble.

(** * Definition 2: Copland data flow semantics%\index{Definition 2: Copland data flow semantics}% *)

Section CoplandFlow.

  (** Compute the label mapping underlying a phrase's data flow
      semantics. *)

  Fixpoint phrase_to_lbls (t : phrase) (p : plc) (ps : pos) (e : evi) : lbls :=
    match t with
    | Cpy => [LCpy p e]
    | Meas msr q tgt =>
        let e' := EMeas msr q tgt p ps e in
        [LMsp p msr q tgt ps e']
    | Sig => [LSig p (ESig p e)]
    | Hsh => [LHsh p (EHsh p e)]
    | At q t' =>
        let e' := phrase_to_evi t' q (0 :: ps) e in
        let l' := phrase_to_lbls t' q (0 :: ps) e in
        [LReq p q e] ++ l' ++ [LRpy q p e']
    | Ln t1 t2 =>
        let e1 := phrase_to_evi t1 p (0 :: ps) e in
        let l1 := phrase_to_lbls t1 p (0 :: ps) e in
        let l2 := phrase_to_lbls t2 p (1 :: ps) e1 in
        l1 ++ l2
    | Br b s t1 t2 =>
        let l1 := phrase_to_lbls t1 p (0 :: ps) (evi_lft s e) in
        let l2 := phrase_to_lbls t2 p (1 :: ps) (evi_rht s e) in
        [LSplt p s e] ++ l1 ++ l2 ++ [LJoin p b (phrase_to_evi t p ps e)]
    end.

  (** A phrase label graph is an IO graph over the phrase's
      [phrase_to_lbls] label mapping. *)

  Definition lbl_graph t p ps e := io_graph (phrase_to_lbls t p ps e).

  (** Compute the data flow semantics of a Copland phrase. *)

  Fixpoint phrase_to_flow (t : phrase) (p : plc) (ps : pos) (e : evi) : lbl_graph t p ps e.
  Proof.
    destruct t.
    - (* Cpy *)
      apply (io_sngl (LCpy p e)).
    - (* Meas *)
      apply (io_sngl (LMsp p msr q tgt ps (EMeas msr q tgt p ps e))).
    - (* Sig *)
      apply (io_sngl (LSig p (ESig p e))).
    - (* Hsh *)
      apply (io_sngl (LHsh p (EHsh p e))).
    - (* At *)
      apply (
          bf_cpy
            (io_sngl (LReq p p0 e))
            (bf_cpy
               (phrase_to_flow t p0 (0 :: ps) e)
               (io_sngl (LRpy p0 p (phrase_to_evi t p0 (0 :: ps) e))))
        ).
    - (* Ln *)
      apply (
          bf_cpy
            (phrase_to_flow t1 p (0 :: ps) e)
            (phrase_to_flow t2 p (1 :: ps) (phrase_to_evi t1 p (0 :: ps) e))
        ).
    - (* Br *)
      apply (
          splt_join s
            (LSplt p s e)
            (phrase_to_flow t1 p (0 :: ps) (evi_lft s e))
            (phrase_to_flow t2 p (1 :: ps) (evi_rht s e))
            (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e))
        ).
  Defined.

  Definition copland_to_flow (c : copland) := phrase_to_flow (snd c) (fst c) [] ENul.

  (** The next two simple lemmas are useful for dealing with the [At]
      and [Br] phrase semantics in place of [simpl] and [unfold], which
      go too far. *)

  Lemma at_phrase_to_flow : forall t p q ps e,
      phrase_to_flow (At q t) p ps e =
        bf_cpy
          (io_sngl (LReq p q e))
          (bf_cpy
             (phrase_to_flow t q (0 :: ps) e)
             (io_sngl (LRpy q p (phrase_to_evi t q (0 :: ps) e)))).
  Proof. reflexivity. Qed.

  Lemma br_phrase_to_flow : forall b s t1 t2 p ps e,
      phrase_to_flow (Br b s t1 t2) p ps e =
        splt_join s
          (LSplt p s e)
          (phrase_to_flow t1 p (0 :: ps) (evi_lft s e))
          (phrase_to_flow t2 p (1 :: ps) (evi_rht s e))
          (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)).
  Proof. reflexivity. Qed.

  (** Expresses [io_evt_lbl] calls for the data flow semantics in
      terms of the underlying [nth_safe] call over the phrase's label
      mapping. *)

  Lemma phrase_io_evt_lbl : forall t p ps e (v : io_evt (phrase_to_flow t p ps e)),
      io_evt_lbl v = nth_safe (phrase_to_lbls t p ps e) v.
  Proof. reflexivity. Qed.

  (** The next two lemmas are special cases of [phrase_io_evt_lbl] for
      [At] and [Br] phrases. *)

  Lemma at_io_evt_lbl :
    forall t p q ps e (v : io_evt (phrase_to_flow (At q t) p ps e)),
      io_evt_lbl v =
        nth_safe
          ([LReq p q e]
             ++ (phrase_to_lbls t q (0 :: ps) e)
             ++ [LRpy q p (phrase_to_evi t q (0 :: ps) e)]) v.
  Proof. reflexivity. Qed.

  Lemma br_io_evt_lbl :
    forall b s t1 t2 p ps e (v : io_evt (phrase_to_flow (Br b s t1 t2) p ps e)),
      io_evt_lbl v =
        nth_safe
          ([LSplt p s e]
             ++ (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
             ++ (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
             ++ [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)]) v.
  Proof. reflexivity. Qed.

  (** Modulo translation, the input event for the [At] phrase is the
      request event. *)

  Lemma at_phrase_input_evt : forall t p q ps e,
      io_input_evt (phrase_to_flow (At q t) p ps e) =
        app_lft
          ((phrase_to_lbls t q (0 :: ps) e) ++ [LRpy q p (phrase_to_evi t q (0 :: ps) e)])
          (io_input_evt (io_sngl (LReq p q e))).
  Proof.
    intros.
    rewrite <- bf_cpy_input_evt with (
        G2 :=
          bf_cpy
            (phrase_to_flow t q (0 :: ps) e)
            (io_sngl (LRpy q p (phrase_to_evi t q (0 :: ps) e)))).
    rewrite at_phrase_to_flow. reflexivity.
  Qed.

  (** Modulo translation, the output event of an [At] phrase's
      semantics is the final reply event. *)

  Lemma at_phrase_output_evt : forall t p q ps e,
      io_output_evt (phrase_to_flow (At q t) p ps e) =
        app_rht
          [LReq p q e]
          (app_rht
             (phrase_to_lbls t q (0 :: ps) e)
             (io_output_evt (io_sngl (LRpy q p (phrase_to_evi t q (0 :: ps) e))))).
  Proof.
    intros.
    rewrite <- bf_cpy_output_evt
      with (G1 := phrase_to_flow t q (0 :: ps) e).
    rewrite <- bf_cpy_output_evt
      with (G1 := io_sngl (LReq p q e)).
    rewrite at_phrase_to_flow.
    reflexivity.
  Qed.

  (** Modulo translation, the output event of a [Br] phrase's
      semantics is the final join event, which we can express in two
      ways. *)

  Lemma br_phrase_output_evt : forall b s t1 t2 p ps e,
      io_output_evt (phrase_to_flow (Br b s t1 t2) p ps e) =
        xsplc_lft
          [LSplt p s e]
          (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
          (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
          [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)]
          (app_rht
             [LSplt p s e]
             (app_rht
                (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
                (io_output_evt (io_sngl (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e))))))
      /\ io_output_evt (phrase_to_flow (Br b s t1 t2) p ps e) =
           xsplc_rht
             [LSplt p s e]
             (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
             (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
             [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)]
             (app_rht
                [LSplt p s e]
                (app_rht
                   (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
                   (io_output_evt (io_sngl (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)))))).
  Proof.
    intros.
    pose proof (
        splt_join_output_evt_full s
          (LSplt p s e)
          (phrase_to_flow t1 p (0 :: ps) (evi_lft s e))
          (phrase_to_flow t2 p (1 :: ps) (evi_rht s e))
          (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e))
      ) as [H0 H1].
    split;
      [rewrite <- H0 | rewrite <- H1];
      rewrite br_phrase_to_flow; auto.
  Qed.

End CoplandFlow.

(** * Definition 1: Data flow graph%\index{Definition 1: Data flow graph}% *)

Section DataFlowGraph.

  (** A data flow graph is a well-formed, acyclic IO graph with
      Copland event labels. *)

  Definition data_flow_graph [l : lbls] (D : io_graph l) :=
    io_graph_well_formed D /\ io_acyclic D.

  (** A phrase's data flow semantics is well-formed. *)

  Lemma phrase_to_flow_well_formed :
    forall t p ps e, io_graph_well_formed (phrase_to_flow t p ps e).
  Proof.
    induction t; intros;
      try (simpl; apply io_sngl_well_formed).
    - (* At *)
      rewrite at_phrase_to_flow.
      apply bf_cpy_well_formed;
        try apply bf_cpy_well_formed;
        try apply io_sngl_well_formed; auto.
    - (* Ln *)
      simpl. apply bf_cpy_well_formed; auto.
    - (* Br *)
      rewrite br_phrase_to_flow.
      apply splt_join_well_formed.
  Qed.

  (** A phrase's data flow semantics is acyclic. *)

  Lemma phrase_to_flow_acyclic :
    forall t p ps e, io_acyclic (phrase_to_flow t p ps e).
  Proof.
    induction t; intros;
      try (simpl; apply io_acyclic_sngl).
    - (* At *)
      rewrite at_phrase_to_flow.
      apply bf_cpy_acyclic;
        try apply bf_cpy_acyclic;
        try apply io_acyclic_sngl; auto.
    - (* Ln *)
      simpl. apply bf_cpy_acyclic; auto.
    - (* Br *)
      rewrite br_phrase_to_flow.
      apply splt_join_acyclic; auto.
  Qed.

  (** A phrase's data flow semantics is a data flow graph. *)

  Theorem phrase_to_flow_data_flow :
    forall t p ps e, data_flow_graph (phrase_to_flow t p ps e).
  Proof.
    split.
    - apply phrase_to_flow_well_formed.
    - apply phrase_to_flow_acyclic.
  Qed.

End DataFlowGraph.

(** * Lemma 1: Flow Graph Top%\index{Lemma 1: Flow Graph Top}% *)

Section FlowGraphTop.

  (** The label evidence of the output event of a phrase's data flow
      semantics equals the phrase's evidence semantics. *)

  Theorem flow_graph_top : forall t p ps e,
      proje (io_evt_lbl (io_output_evt (phrase_to_flow t p ps e))) = phrase_to_evi t p ps e.
  Proof.
    induction t; intros; auto.
    - (* At *)
      rewrite at_io_evt_lbl.
      rewrite at_phrase_output_evt.
      repeat rewrite app_rht_nth_safe.
      rewrite nth_safe_sngl. auto.
    - (* Ln *)
      simpl. rewrite bf_cpy_output_evt.
      rewrite app_rht_evt_lbl_bf_cpy.
      rewrite IHt2. reflexivity.
    - (* Br *)
      rewrite br_io_evt_lbl.
      pose proof (
          br_phrase_output_evt b s t1 t2 p ps e
        ) as [H _].
      rewrite H.
      rewrite xsplc_lft_nth_safe.
      repeat rewrite app_rht_nth_safe.
      rewrite nth_safe_sngl. auto.
  Qed.

End FlowGraphTop.

(** * Place *)

Section Place.

  (** The sending place of the input event is the starting place. *)

  Lemma phrase_to_flow_input_sendp : forall t p ps e,
      sendp (io_evt_lbl (io_input_evt (phrase_to_flow t p ps e))) = p.
  Proof with auto.
    induction t; intros; try reflexivity.
    - (* At *)
      rewrite at_phrase_input_evt.
      rewrite at_io_evt_lbl.
      rewrite app_lft_nth_safe...
    - (* Ln *)
      rewrite phrase_io_evt_lbl; simpl.
      unfold io_evt_lbl in IHt1.
      rewrite bf_cpy_input_evt.
      rewrite app_lft_nth_safe...
  Qed.

  Corollary phrase_to_flow_input_sendp' : forall t p ps e,
      sendp (nth_safe (phrase_to_lbls t p ps e) (io_input_evt (phrase_to_flow t p ps e))) = p.
  Proof. exact phrase_to_flow_input_sendp. Qed.

  (** The receiving place of the output event is the starting place. *)

  Lemma phrase_to_flow_output_recvp : forall t p ps e,
      recvp (io_evt_lbl (io_output_evt (phrase_to_flow t p ps e))) = p.
  Proof with auto.
    induction t; intros; try reflexivity.
    - (* At *)
      rewrite at_phrase_output_evt.
      rewrite at_io_evt_lbl.
      repeat rewrite app_rht_nth_safe...
    - (* Ln *)
      rewrite phrase_io_evt_lbl; simpl.
      unfold io_evt_lbl in IHt2.
      rewrite bf_cpy_output_evt.
      rewrite app_rht_nth_safe...
    - (* Br *)
      pose proof (
          br_phrase_output_evt b s t1 t2 p ps e
        ) as [H _]; rewrite H.
      rewrite br_io_evt_lbl.
      rewrite xsplc_lft_nth_safe.
      repeat rewrite app_rht_nth_safe...
  Qed.

  Corollary phrase_to_flow_output_recvp' : forall t p ps e,
      recvp (nth_safe (phrase_to_lbls t p ps e) (io_output_evt (phrase_to_flow t p ps e))) = p.
  Proof. exact phrase_to_flow_output_recvp. Qed.

  (** ** Non-teleportation properties *)

  Section NoTeleport.

    (** The "no-teleportation" property for [evt_seq] of Copland labels:
        successive labels have the [plc_adj] property. *)

    Definition no_teleport [l : lbls] (pi : evt_seq l) : Prop :=
      forall i j,
        idx_nat j = S (idx_nat i) ->
        plc_adj (nth_safe l (nth_safe pi i)) (nth_safe l (nth_safe pi j)).

    (** A reversed definition of [no_teleport] for use with [rev_path]. *)

    Definition rev_no_teleport [l : lbls] (pi : evt_seq l) : Prop :=
      forall i j,
        idx_nat j = S (idx_nat i) ->
        plc_adj (nth_safe l (nth_safe pi j)) (nth_safe l (nth_safe pi i)).

    Lemma no_teleport_rev :
      forall [l : lbls] (pi : evt_seq l),
        no_teleport pi <-> rev_no_teleport (rev pi).
    Proof.
      unfold no_teleport, rev_no_teleport, plc_adj.
      split; intros.
      - destruct (rev_idx_preimage pi i) as [i' Hi].
        destruct (rev_idx_preimage pi j) as [j' Hj].
        subst i j.
        repeat rewrite (@nth_safe_rev _ pi).
        assert (idx_nat i' = S (idx_nat j')).
        { destruct i'; destruct j'; simpl in *; lia. }
        apply H; auto.
      - repeat rewrite <- (@nth_safe_rev _ pi).
        apply H. destruct i; destruct j; simpl in *; lia.
    Qed.

    (** Removing an element from the front of a [rev_no_teleport]
        sequence does not change this property. *)

    Lemma rev_no_teleport_cons :
      forall [l : lbls] (pi : evt_seq l) v,
        rev_no_teleport (v :: pi) -> rev_no_teleport pi.
    Proof.
      unfold rev_no_teleport; intros.
      rewrite (to_idx_nat_evi i) in *.
      rewrite (to_idx_nat_evi j) in *.
      destruct i as [n Hn]; destruct j as [m Hm].
      simpl idx_evi in *; simpl in H0; subst m.
      assert (S n < length (v :: pi)) by (simpl; lia).
      assert (S (S n) < length (v :: pi)) by (simpl in *; lia).
      pose proof (H (to_idx H0) (to_idx H1)).
      intuition.
      rewrite (nth_safe_cons H0 Hn) in H3.
      rewrite (nth_safe_cons H1 Hm) in H3.
      assumption.
    Qed.

    (** In a [rev_no_teleport] event sequence, if [j < i] index events
        such that the [j] sending place is different from the [i]
        receiving place, then [j] and [i] are separated by a
        cross-place communication event whose sending place is the
        same as the [i] receiving place. *)

    Lemma rev_xplc_comm_between :
      forall [l : lbls] pi i j,
        rev_no_teleport pi ->
        idx_nat j < idx_nat i ->
        sendp (nth_safe l (nth_safe pi j))
        <> recvp (nth_safe l (nth_safe pi i)) ->
        exists k,
          idx_nat j < idx_nat k < idx_nat i
          /\ xplc_comm_lbl (nth_safe l (nth_safe pi k))
          /\ sendp (nth_safe l (nth_safe pi k))
             = recvp (nth_safe l (nth_safe pi i)).
    Proof.
      induction pi; intros;
        try (destruct i; simpl in *; lia).
      rewrite (to_idx_nat_evi i) in *.
      rewrite (to_idx_nat_evi j) in *.
      destruct i as [n Hn]; destruct j as [m Hm].
      simpl idx_evi in *; simpl idx_nat in *.
      destruct m; destruct n; try lia.
      - destruct pi as [|a' pi]; destruct n; try (simpl in *; lia).
        + simpl in H1.
          pose proof (H (to_idx Hm) (to_idx Hn)).
          simpl in H2; intuition; unfold plc_adj in H3.
          symmetry in H3. contradiction.
        + assert (Hz : 1 < length (a :: a' :: pi)) by (simpl; lia).
          destruct (
              xplc_comm_lblb (nth_safe l (nth_safe (a :: a' :: pi) (to_idx Hz)))
            ) eqn:Hx;
            [ | apply Bool.not_true_iff_false in Hx];
            rewrite <- xplc_comm_lbl_reflect in Hx.
          * destruct n; destruct pi as [|a'' pi]; try (simpl in *; lia).
            -- simpl in H1, Hx.
               pose proof (H (to_idx Hz) (to_idx Hn)). intuition.
               unfold plc_adj in H3; simpl in H3.
               exists (to_idx Hz). simpl. intuition.
            -- destruct (
                   String.string_dec
                     (sendp (nth_safe l (nth_safe (a :: a' :: a'' :: pi) (to_idx Hz))))
                     (recvp (nth_safe l (nth_safe (a :: a' :: a'' :: pi) (to_idx Hn))))
                 ).
               ++ exists (to_idx Hz). simpl; repeat split; auto; lia.
               ++ assert (0 < length (a' :: a'' :: pi)) by (simpl; lia).
                  assert (S (S n) < length (a' :: a'' :: pi)) by (simpl in *; lia).
                  rewrite (nth_safe_cons _ H3) in H1, n0.
                  rewrite (nth_safe_cons _ H2) in n0.
                  assert (idx_nat (to_idx H2) < idx_nat (to_idx H3)) by (simpl; lia).
                  apply rev_no_teleport_cons in H.
                  pose proof (IHpi _ _ H H4 n0).
                  destruct H5 as [k [H5 [H6 H7]]].
                  rewrite (to_idx_nat_evi k) in *.
                  destruct k as [y Hy']; simpl idx_evi in *; simpl in H5.
                  assert (Hy : S y < length (a :: a' :: a'' :: pi)) by (simpl in *; lia).
                  rewrite <- (nth_safe_cons Hy) in H6, H7.
                  rewrite <- (nth_safe_cons Hn) in H7.
                  exists (to_idx Hy). simpl; repeat split; auto; lia.
          * apply not_xplc_comm_lbl in Hx.
            pose proof (H (to_idx Hm) (to_idx Hz)).
            intuition; unfold plc_adj in H3.
            rewrite <- H3 in H1; rewrite <- Hx in H1.
            assert (Hz' : 0 < length (a' :: pi)) by (simpl; lia).
            assert (Hn' : S n < length (a' :: pi)) by (simpl in *; lia).
            rewrite (nth_safe_cons _ Hz') in H1.
            rewrite (nth_safe_cons _ Hn') in H1.
            assert (idx_nat (to_idx Hz') < idx_nat (to_idx Hn')) by (simpl; lia).
            apply rev_no_teleport_cons in H.
            pose proof (IHpi _ _ H H2 H1).
            destruct H4 as [k [H4 [H5 H6]]].
            rewrite (to_idx_nat_evi k) in *.
            destruct k as [y Hy']; simpl idx_evi in *; simpl in H4.
            assert (Hy : S y < length (a :: a' :: pi)) by (simpl in *; lia).
            rewrite <- (nth_safe_cons Hy) in H5, H6.
            rewrite <- (nth_safe_cons Hn) in H6.
            exists (to_idx Hy). simpl; repeat split; auto; lia.
      - assert (Hn' : n < length pi) by (simpl in *; lia).
        assert (Hm' : m < length pi) by (simpl in *; lia).
        assert (idx_nat (to_idx Hm') < idx_nat (to_idx Hn')) by (simpl; lia).
        rewrite (nth_safe_cons _ Hn') in H1.
        rewrite (nth_safe_cons _ Hm') in H1.
        apply rev_no_teleport_cons in H.
        pose proof (IHpi _ _ H H2 H1).
        destruct H3 as [k [H3 [H4 H5]]].
        rewrite (to_idx_nat_evi k) in *.
        destruct k as [z Hz']; simpl idx_evi in *; simpl idx_nat in *.
        assert (Hz : S z < length (a :: pi)) by (simpl; lia).
        rewrite <- (nth_safe_cons Hz) in H4, H5.
        rewrite <- (nth_safe_cons Hn) in H5.
        exists (to_idx Hz). simpl; repeat split; auto; lia.
    Qed.

    (** For a flow edge [(v, v')] through the data flow semantics, the
        labels of [v] and [v'] have the [plc_adj] property. *)

    Lemma phrase_to_flow_edge_plc_adj :
      forall t p ps e (v v' : io_evt (phrase_to_flow t p ps e)),
        In (v, v') (io_to_graph (phrase_to_flow t p ps e)) ->
        plc_adj (io_evt_lbl v) (io_evt_lbl v').
    Proof with auto.
      unfold plc_adj.
      induction t; intros;
        try (simpl in *; contradiction).
      - (* At *)
        rewrite at_phrase_to_flow in H.
        apply bf_cpy_cpy_sngls_edge in H as
            [[H H']|[[u [u' [H [H' H'']]]]|[H H']]];
          repeat rewrite at_io_evt_lbl; subst;
          repeat rewrite app_rht_nth_safe;
          repeat rewrite app_lft_nth_safe;
          unfold io_evt_lbl in *;
          try rewrite phrase_to_flow_input_sendp';
          try rewrite phrase_to_flow_output_recvp'...
      - (* Ln *)
        repeat rewrite phrase_io_evt_lbl; simpl in *.
        apply bf_cpy_edge in H as
            [[H H'] |
              [ [u [u' [H [H' H'']]]] |
                [u [u' [H [H' H'']]]]]]; subst;
          repeat rewrite app_lft_nth_safe;
          repeat rewrite app_rht_nth_safe.
        + rewrite phrase_to_flow_input_sendp'.
          rewrite phrase_to_flow_output_recvp'...
        + apply IHt1...
        + apply IHt2...
      - (* Br *)
        rewrite br_phrase_to_flow in H.
        repeat rewrite br_io_evt_lbl.
        apply splt_join_edge in H as
            [ [u [u' [H [H' H'']]]] |
              [u [u' [H [H' H'']]]] ]; subst;
          [ repeat rewrite xsplc_lft_nth_safe;
            unfold splt_join_lft in H |
            repeat rewrite xsplc_rht_nth_safe;
            unfold splt_join_rht in H ];
          destruct s;
          try (apply bf_cpy_cpy_sngls_edge in H as
                [[H H']|[[w [w' [H [H' H'']]]]|[H H']]]);
          try (apply bf_nil_cpy_sngls_edge in H as
                [[w [w' [H [H' H'']]]]|[H H']]); subst;
          repeat rewrite app_rht_nth_safe;
          repeat rewrite app_lft_nth_safe;
          try rewrite phrase_to_flow_input_sendp';
          try rewrite phrase_to_flow_output_recvp';
          try apply IHt1; try apply IHt2...
    Qed.

    (** Every path through the data flow semantics is non-teleporting. *)

    Lemma phrase_to_flow_path_no_teleport :
      forall t p ps e pi,
        io_path (phrase_to_flow t p ps e) pi -> no_teleport pi.
    Proof.
      unfold no_teleport.
      intros t p ps e pi H.
      induction H; intros;
        try (repeat rewrite idx_sngl in H; lia).
      rewrite (to_idx_nat_evi i) in *.
      rewrite (to_idx_nat_evi j) in *.
      destruct i as [n Hn]; destruct j as [m Hm].
      simpl idx_evi in *; simpl idx_nat in *.
      destruct n; subst.
      - simpl. apply phrase_to_flow_edge_plc_adj; auto.
      - assert (Hn' : n < length (v' :: pi)) by (simpl in *; lia).
        assert (Hm' : S n < length (v' :: pi)) by (simpl in *; lia).
        rewrite (nth_safe_cons _ Hn').
        rewrite (nth_safe_cons _ Hm').
        apply IHpath. simpl; lia.
    Qed.

  End NoTeleport.

End Place.

(** * Coherent Copland event sequences *)

Section Coherent.

  (** ** Evidence-passing event sequences *)

  Section EviPassing.

    (** The evidence-passing property for [evt_seq] of Copland labels:
        the evidence output at each event in the sequence is passed as
        input to the event that immediately follows. *)

    Definition evi_passing_seq [l : lbls] (pi : evt_seq l) : Prop :=
      forall i j,
        idx_nat j = S (idx_nat i) ->
        evi_passing (nth_safe l (nth_safe pi i)) (nth_safe l (nth_safe pi j)).

    (** A reversed definition of [evi_passing_seq] for use with
        [rev_path]. *)

    Definition rev_evi_passing_seq [l : lbls] (pi : evt_seq l) : Prop :=
      forall i j,
        idx_nat j = S (idx_nat i) ->
        evi_passing (nth_safe l (nth_safe pi j)) (nth_safe l (nth_safe pi i)).

    Lemma evi_passing_seq_rev :
      forall [l : lbls] (pi : evt_seq l),
        evi_passing_seq pi <-> rev_evi_passing_seq (rev pi).
    Proof.
      unfold evi_passing_seq, rev_evi_passing_seq, evi_passing.
      split; intros.
      - destruct (rev_idx_preimage pi i) as [i' Hi].
        destruct (rev_idx_preimage pi j) as [j' Hj].
        subst i j.
        repeat rewrite (@nth_safe_rev _ pi).
        assert (idx_nat i' = S (idx_nat j')).
        { destruct i'; destruct j'; simpl in *; lia. }
        apply H; auto.
      - repeat rewrite <- (@nth_safe_rev _ pi).
        apply H. destruct i; destruct j; simpl in *; lia.
    Qed.

    (** Removing an element from the front of a [rev_evi_passing_seq]
        sequence does not change this property. *)

    Lemma rev_evi_passing_seq_cons :
      forall [l : lbls] (pi : evt_seq l) v,
        rev_evi_passing_seq (v :: pi) -> rev_evi_passing_seq pi.
    Proof.
      unfold rev_evi_passing_seq; intros.
      rewrite (to_idx_nat_evi i) in *.
      rewrite (to_idx_nat_evi j) in *.
      destruct i as [n Hn]; destruct j as [m Hm].
      simpl idx_evi in *; simpl in H0; subst m.
      assert (S n < length (v :: pi)) by (simpl in *; lia).
      assert (S (S n) < length (v :: pi)) by (simpl in *; lia).
      pose proof (H (to_idx H0) (to_idx H1)).
      intuition.
      rewrite (nth_safe_cons H0 Hn) in H3.
      rewrite (nth_safe_cons H1 Hm) in H3.
      assumption.
    Qed.

    (** The input evidence to the phrase is the input evidence to the
        input event of the phrase's semantics. *)

    Lemma phrase_to_flow_input_proje_in :
      forall t p ps e,
        proje_in (io_evt_lbl (io_input_evt (phrase_to_flow t p ps e))) = (e, e).
    Proof.
      induction t; intros; auto.
      - rewrite at_phrase_input_evt. auto.
      - simpl. rewrite bf_cpy_input_evt.
        unfold io_evt_lbl in *.
        rewrite app_lft_nth_safe. auto.
    Qed.

    (** Labels in data flow semantics edge events are [evi_passing]. *)

    Lemma phrase_to_flow_evi_passing_edge :
      forall t p ps e (v v' : io_evt (phrase_to_flow t p ps e)),
        In (v, v') (io_to_graph (phrase_to_flow t p ps e)) ->
        evi_passing (io_evt_lbl v) (io_evt_lbl v').
    Proof.
      unfold evi_passing.
      induction t; intros; try (simpl in *; contradiction).
      - rewrite at_phrase_to_flow in H.
        apply bf_cpy_cpy_sngls_edge in H.
        destruct H as
          [[H H']|[[u [u' [H [H' H'']]]]|[H H']]];
          subst; repeat rewrite at_io_evt_lbl;
          repeat rewrite app_rht_nth_safe;
          repeat rewrite app_lft_nth_safe.
        + simpl. rewrite <- phrase_io_evt_lbl.
          rewrite phrase_to_flow_input_proje_in; auto.
        + apply IHt; auto.
        + rewrite <- phrase_io_evt_lbl.
          rewrite flow_graph_top. simpl; auto.
      - simpl in H. apply bf_cpy_edge in H.
        repeat rewrite phrase_io_evt_lbl; simpl.
        destruct H as
          [[H H'] |
            [ [u [u' [H [H' H'']]]] |
              [u [u' [H [H' H'']]]] ]]; subst;
          try (repeat rewrite app_rht_nth_safe);
          try (repeat rewrite app_lft_nth_safe);
          try apply IHt1; try apply IHt2; auto.
        repeat rewrite <- phrase_io_evt_lbl.
        rewrite phrase_to_flow_input_proje_in.
        rewrite flow_graph_top. auto.
      - rewrite br_phrase_to_flow in H.
        repeat rewrite br_io_evt_lbl.
        apply splt_join_edge in H as
            [ [u [u' [H [H' H'']]]] |
              [u [u' [H [H' H'']]]] ]; subst.
        + repeat rewrite xsplc_lft_nth_safe.
          unfold splt_join_lft in H; destruct s;
            try (apply bf_cpy_cpy_sngls_edge in H as
                  [[H H']|[[w [w' [H [H' H'']]]]|[H H']]]);
            try (apply bf_nil_cpy_sngls_edge in H as
                  [[w [w' [H [H' H'']]]]|[H H']]); subst;
            try repeat rewrite app_rht_nth_safe;
            try repeat rewrite app_lft_nth_safe;
            try (apply IHt1; auto);
            try repeat rewrite <- phrase_io_evt_lbl;
            try (repeat rewrite phrase_to_flow_input_proje_in; auto);
            try (repeat rewrite flow_graph_top;
                 destruct b; simpl; auto).
        + repeat rewrite xsplc_rht_nth_safe.
          unfold splt_join_rht in H; destruct s;
            try (apply bf_cpy_cpy_sngls_edge in H as
                  [[H H']|[[w [w' [H [H' H'']]]]|[H H']]]);
            try (apply bf_nil_cpy_sngls_edge in H as
                  [[w [w' [H [H' H'']]]]|[H H']]); subst;
            try repeat rewrite app_rht_nth_safe;
            try repeat rewrite app_lft_nth_safe;
            try (apply IHt2; auto);
            try repeat rewrite <- phrase_io_evt_lbl;
            try (repeat rewrite phrase_to_flow_input_proje_in; auto);
            try (repeat rewrite flow_graph_top;
                 destruct b; simpl; auto).
    Qed.

    (** Paths through the data flow semantics are [evi_passing_seq]. *)

    Lemma phrase_to_flow_path_evi_passing :
      forall t p ps e pi,
        io_path (phrase_to_flow t p ps e) pi -> evi_passing_seq pi.
    Proof.
      unfold evi_passing_seq; intros.
      induction H.
      - repeat rewrite idx_sngl in H0. lia.
      - rewrite (to_idx_nat_evi i) in *.
        rewrite (to_idx_nat_evi j) in *.
        destruct i as [n Hn];
          destruct j as [m Hm].
        simpl idx_evi in *; simpl in H0.
        destruct n; subst m.
        + simpl. apply phrase_to_flow_evi_passing_edge. auto.
        + assert (Hn' : n < length (v' :: pi)) by (simpl in *; lia).
          assert (Hm' : S n < length (v' :: pi)) by (simpl in *; lia).
          assert (
              idx_nat (to_idx Hm') = S (idx_nat (to_idx Hn'))
            ) by (simpl; lia).
          apply IHpath in H0.
          rewrite <- (nth_safe_cons Hn) in H0.
          rewrite <- (nth_safe_cons Hm) in H0.
          assumption.
    Qed.

  End EviPassing.

  (** ** Valid event sequences *)

  Section Valid.

    (** The valid property for [evt_seq] of Copland labels: the label of
        every edge is valid with respect to [valid_lbl]. *)

    Definition valid_lbl_seq [l : lbls] (pi : evt_seq l) : Prop :=
      forall i, valid_lbl (nth_safe l (nth_safe pi i)).

    (** An event sequence is valid iff its reverse is. *)

    Lemma valid_lbl_seq_rev :
      forall [l : lbls] (pi : evt_seq l),
        valid_lbl_seq pi <-> valid_lbl_seq (rev pi).
    Proof.
      unfold valid_lbl_seq. split; intros.
      - destruct (rev_idx_preimage pi i) as [i' H'].
        subst. rewrite nth_safe_rev. auto.
      - rewrite <- (@nth_safe_rev _ pi). auto.
    Qed.

    (** Removing an element from the front of a [valid_lbl_seq] sequence
        does not change this property. *)

    Lemma valid_lbl_seq_cons :
      forall [l : lbls] (pi : evt_seq l) v,
        valid_lbl_seq (v :: pi) -> valid_lbl_seq pi.
    Proof.
      unfold valid_lbl_seq; intros.
      rewrite (to_idx_nat_evi i) in *.
      destruct i as [n Hn]; simpl.
      assert (S n < length (v :: pi)) by (simpl in *; lia).
      pose proof (H (to_idx H0)).
      rewrite (nth_safe_cons H0 Hn) in H1.
      assumption.
    Qed.

    (** Every event label in the data flow semantics is valid. *)

    Lemma phrase_to_flow_lbl_valid :
      forall t p ps e (v : io_evt (phrase_to_flow t p ps e)),
        valid_lbl (io_evt_lbl v).
    Proof.
      unfold valid_lbl.
      induction t;
        try (
            intros; simpl in *;
            rewrite io_sngl_evt_lbl; simpl;
            repeat rewrite String.eqb_refl
          ); auto.
      - simpl. apply list_eqb_refl.
      - intros q ps e.
        rewrite at_phrase_to_flow; intros.
        destruct (evt_lbl_bf_cpy _ _ v) as [[u H]|[u H]];
          assert (H0 : valid_lblb (io_evt_lbl v) = valid_lblb (io_evt_lbl u))
          by (rewrite <- H; auto); rewrite H0; clear H0 H v.
        + rewrite io_sngl_evt_lbl. auto.
        + destruct (evt_lbl_bf_cpy _ _ u) as [[u' H']|[u' H']];
            assert (H1 : valid_lblb (io_evt_lbl u) = valid_lblb (io_evt_lbl u'))
            by (rewrite <- H'; auto); rewrite H1; clear H1 H' u;
            try rewrite io_sngl_evt_lbl; auto.
      - simpl; intros.
        destruct (evt_lbl_bf_cpy _ _ v) as [[u H]|[u H]];
          rewrite H; try apply IHt1; try apply IHt2.
      - intros p ps e. rewrite br_phrase_to_flow; intros.
        destruct (evt_lbl_splt_join_br v) as [[u H]|[u H]];
          assert (H0: valid_lblb (io_evt_lbl v) = valid_lblb (io_evt_lbl u))
          by (rewrite <- H; auto); rewrite H0; clear H0 H v;
          destruct s; unfold splt_join_lft in *; unfold splt_join_rht in *;
          try (destruct (evt_lbl_bf_cpy _ _ u) as [[u' H']|[u' H']]);
          try (destruct (evt_lbl_bf_nil _ _ u) as [[u' H']|[u' H']]);
          rewrite H'; try (rewrite io_sngl_evt_lbl; auto);
          destruct (evt_lbl_bf_cpy _ _ u') as [[u'' H'']|[u'' H'']];
          rewrite H''; try apply IHt1; try apply IHt2;
          rewrite io_sngl_evt_lbl; destruct b; simpl; auto.
    Qed.

    (** Every path through the data flow semantics is valid. *)

    Lemma phrase_to_flow_path_valid :
      forall t p ps e pi,
        io_path (phrase_to_flow t p ps e) pi -> valid_lbl_seq pi.
    Proof.
      unfold valid_lbl_seq; intros.
      induction H.
      - rewrite nth_safe_sngl.
        apply phrase_to_flow_lbl_valid.
      - rewrite (to_idx_nat_evi i) in *.
        destruct i as [n Hn]; simpl idx_evi in *.
        destruct n.
        + simpl. apply phrase_to_flow_lbl_valid.
        + assert (n < length (v' :: pi)) by (simpl in *; lia).
          pose proof (IHpath (to_idx H1)).
          rewrite <- (nth_safe_cons Hn) in H2; auto.
    Qed.

  End Valid.

  (** ** Coherent sequences and graphs *)

  (** Finally, a coherent event sequence is both valid and
      evidence-passing. *)

  Definition coherent [l : lbls] (pi : evt_seq l) :=
    valid_lbl_seq pi /\ evi_passing_seq pi.

  (** A coherent IO graph is one whose paths are coherent. *)

  Definition coherent_graph [l : lbls] (G : io_graph l) :=
    forall pi, io_path G pi -> coherent pi.

  (** Reversed definitions of [coherent] and [coherent_graph] for use
      with [rev_path]. *)

  Definition rev_coherent [l : lbls] (pi : evt_seq l) :=
    valid_lbl_seq pi /\ rev_evi_passing_seq pi.

  Definition rev_coherent_graph [l : lbls] (G : io_graph l) :=
    forall pi, io_rev_path G pi -> rev_coherent pi.

  Lemma coherent_iff_rev_coherent_rev :
    forall l (pi : evt_seq l),
      coherent pi <-> rev_coherent (rev pi).
  Proof.
    unfold coherent, rev_coherent.
    intros. rewrite <- valid_lbl_seq_rev.
    rewrite <- evi_passing_seq_rev. reflexivity.
  Qed.

  (** An IO graph is coherent iff it is reverse-coherent. *)

  Lemma coherent_graph_iff_rev_coherent_graph :
    forall l (G : io_graph l),
      coherent_graph G <-> rev_coherent_graph G.
  Proof.
    unfold coherent_graph, rev_coherent_graph.
    split; intros.
    - replace pi with (rev (rev pi)) in *;
        try apply rev_involutive.
      apply io_path_iff_rev_path_rev in H0.
      apply H in H0.
      apply coherent_iff_rev_coherent_rev; auto.
    - apply io_path_iff_rev_path_rev in H0.
      apply H in H0.
      apply coherent_iff_rev_coherent_rev; auto.
  Qed.

  (** The Copland data flow semantics are coherent graphs. *)

  Lemma phrase_to_flow_coherent :
    forall t p ps e,
      coherent_graph (phrase_to_flow t p ps e).
  Proof.
    unfold coherent_graph, coherent; split.
    - apply phrase_to_flow_path_valid; auto.
    - apply phrase_to_flow_path_evi_passing; auto.
  Qed.

End Coherent.

(** * Accumulating properties *)

Section Accm.

  (** The accumulating property for [evt_seq] of Copland labels: if
      [v] occurs earlier in the sequence than [v'], then the label
      evidence of [v] is a subterm of that of [v']. *)

  Definition accm [l : lbls] (pi : evt_seq l) :=
    forall i j (v v' : idx l),
      v = nth_safe pi i ->
      v' = nth_safe pi j ->
      idx_nat i < idx_nat j ->
      subterm (proje (nth_safe l v)) (proje (nth_safe l v')).

  (** The accumulating property for IO graphs with Copland labels:
      every path through the graph is accumulating. *)

  Definition accm_graph [l : lbls] (G : io_graph l) :=
    forall pi, io_path G pi -> accm pi.

  (** A singleton event sequence is accumulating. *)

  Lemma accm_evt_seq_sngl :
    forall [l : lbls] (v : idx l), accm [v].
  Proof.
    unfold accm; intros.
    pose proof (idx_sngl i).
    pose proof (idx_sngl j).
    lia.
  Qed.

  (** The input evidence is always a subterm of the input event label
      evidence for the data flow semantics. *)

  Lemma phrase_to_flow_input_evi_subterm :
    forall t p ps e,
      subterm e (proje (io_evt_lbl (io_input_evt (phrase_to_flow t p ps e)))).
  Proof.
    induction t; intros;
      try rewrite at_phrase_input_evt;
      simpl; auto.
    (* Ln *)
    rewrite bf_cpy_input_evt.
    rewrite app_lft_evt_lbl_bf_cpy.
    apply IHt1.
  Qed.

  (** Proof of [phrase_to_flow_edge_subterm] for the left branch of
      [Br] semantics. *)

  Lemma br_phrase_lft_edge_subterm :
    forall b s t1 t2,
      (forall p ps e (v v' : io_evt (phrase_to_flow t1 p ps e)),
          In (v, v') (io_to_graph (phrase_to_flow t1 p ps e)) ->
          subterm (proje (io_evt_lbl v)) (proje (io_evt_lbl v'))) ->
      (forall p ps e (v v' : io_evt (
                                 splt_join_lft s
                                   (LSplt p s e)
                                   (phrase_to_flow t1 p (0 :: ps) (evi_lft s e))
                                   (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)))),
          In (v, v') (io_to_graph (
                          splt_join_lft s
                            (LSplt p s e)
                            (phrase_to_flow t1 p (0 :: ps) (evi_lft s e))
                            (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)))) ->
          subterm (proje (io_evt_lbl v)) (proje (io_evt_lbl v'))).
  Proof.
    destruct s; unfold splt_join_lft; intros;
      try (apply bf_cpy_cpy_sngls_edge in H0 as
            [[H0 H0']|[[u [u' [H0 [H0' H0'']]]]|[H0 H0']]]);
      try (apply bf_nil_cpy_sngls_edge in H0 as
            [[u [u' [H0 [H0' H0'']]]]|[H0 H0']]); subst;
      try (repeat rewrite app_rht_evt_lbl_bf_nil);
      try (repeat rewrite app_rht_evt_lbl_bf_cpy);
      try (repeat rewrite app_lft_evt_lbl_bf_cpy);
      try (simpl; apply phrase_to_flow_input_evi_subterm);
      try (rewrite flow_graph_top; destruct b; simpl; auto);
      try (simpl in *; intuition).
  Qed.

  (** Proof of [phrase_to_flow_edge_subterm] for the right branch of
      [Br] semantics.

      Note that we cannot use a symmetry argument here because the 0
      versus 1 position distinguishers in evidence for the left and
      right branches prevent us from reusing the previous result.  It
      would be worth exploring alternative proof strategies that could
      use symmetry in the future. *)

  Lemma br_phrase_rht_edge_subterm :
    forall b s t1 t2,
      (forall p ps e (v v' : io_evt (phrase_to_flow t2 p ps e)),
          In (v, v') (io_to_graph (phrase_to_flow t2 p ps e)) ->
          subterm (proje (io_evt_lbl v)) (proje (io_evt_lbl v'))) ->
      (forall p ps e (v v' : io_evt (
                                 splt_join_rht s
                                   (LSplt p s e)
                                   (phrase_to_flow t2 p (1 :: ps) (evi_rht s e))
                                   (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)))),
          In (v, v') (io_to_graph (
                          splt_join_rht s
                            (LSplt p s e)
                            (phrase_to_flow t2 p (1 :: ps) (evi_rht s e))
                            (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)))) ->
          subterm (proje (io_evt_lbl v)) (proje (io_evt_lbl v'))).
  Proof.
    destruct s; unfold splt_join_rht; intros;
      try (apply bf_cpy_cpy_sngls_edge in H0 as
            [[H0 H0']|[[u [u' [H0 [H0' H0'']]]]|[H0 H0']]]);
      try (apply bf_nil_cpy_sngls_edge in H0 as
            [[u [u' [H0 [H0' H0'']]]]|[H0 H0']]); subst;
      try (repeat rewrite app_rht_evt_lbl_bf_nil);
      try (repeat rewrite app_rht_evt_lbl_bf_cpy);
      try (repeat rewrite app_lft_evt_lbl_bf_cpy);
      try (simpl; apply phrase_to_flow_input_evi_subterm);
      try (rewrite flow_graph_top; destruct b; simpl; auto);
      try (simpl in *; intuition).
  Qed.

  (** For the data flow semantics, label evidence respects the subterm
      relation along edges. *)

  Lemma phrase_to_flow_edge_subterm :
    forall t p ps e (v v' : io_evt (phrase_to_flow t p ps e)),
      In (v, v') (io_to_graph (phrase_to_flow t p ps e)) ->
      subterm (proje (io_evt_lbl v)) (proje (io_evt_lbl v')).
  Proof.
    induction t; intros;
      try (simpl in *; contradiction).
    - (* At *)
      rewrite at_phrase_to_flow in H.
      apply bf_cpy_cpy_sngls_edge in H as
          [[H H']|[[u [u' [H [H' H'']]]]|[H H']]];
        subst;
        repeat rewrite at_io_evt_lbl;
        repeat (try rewrite app_rht_nth_safe);
        repeat (try rewrite app_lft_nth_safe); simpl.
      + apply phrase_to_flow_input_evi_subterm.
      + apply IHt; auto.
      + rewrite <- phrase_io_evt_lbl.
        rewrite flow_graph_top; auto.
    - (* Ln *)
      simpl in *.
      apply bf_cpy_edge in H.
      destruct H as [
          [H H'] |
          [ [v1 [v1' [H [H' H'']]]] |
            [v2 [v2' [H [H' H'']]]]]];
        subst.
      + rewrite app_lft_evt_lbl_bf_cpy.
        rewrite app_rht_evt_lbl_bf_cpy.
        rewrite flow_graph_top.
        apply phrase_to_flow_input_evi_subterm.
      + repeat rewrite app_lft_evt_lbl_bf_cpy.
        apply IHt1; auto.
      + repeat rewrite app_rht_evt_lbl_bf_cpy.
        apply IHt2; auto.
    - (* Br *)
      rewrite br_phrase_to_flow in H.
      apply splt_join_edge in H.
      destruct H as [
          [u [u' [H [H' H'']]]] |
          [u [u' [H [H' H'']]]]];
        subst; repeat rewrite br_io_evt_lbl.
      + (* Lft *)
        repeat rewrite xsplc_lft_nth_safe.
        pose proof (
            br_phrase_lft_edge_subterm b s t1 t2 IHt1
          ).
        apply H0; auto.
      + (* Rht *)
        repeat rewrite xsplc_rht_nth_safe.
        pose proof (
            br_phrase_rht_edge_subterm b s t1 t2 IHt2
          ).
        apply H0; auto.
  Qed.

  (** The data flow semantics is always an accumulating graph. *)

  Theorem phrase_to_flow_accm_graph :
    forall t p ps e, accm_graph (phrase_to_flow t p ps e).
  Proof.
    unfold accm_graph; intros.
    induction H;
      try apply accm_evt_seq_sngl.
    unfold accm in *; intros.
    rewrite (to_idx_nat_evi i) in H1.
    rewrite (to_idx_nat_evi j) in H2.
    destruct i as [n Hn];
      destruct j as [m Hm].
    simpl idx_evi in H1, H2. simpl in H3.
    destruct n; destruct m; try lia.
    - (* n = 0, m > 0 *)
      simpl in H1. subst v0.
      destruct m.
      + (* m = 1, v'0 = v' *)
        simpl in H2. subst v'0.
        apply phrase_to_flow_edge_subterm; auto.
      + (* m > 1 *)
        assert (0 < S m) by lia.
        assert (0 < length (v' :: pi))
          by (simpl; lia).
        assert (Hm' : S m < length (v' :: pi))
          by (simpl in *; lia).
        assert (v'0 = nth_safe (v' :: pi) (to_idx Hm')).
        { rewrite <- (nth_safe_cons Hm Hm'); auto. }
        (* Use subterm transitivity through v' *)
        eapply subterm_trans.
        * apply phrase_to_flow_edge_subterm; eauto.
        * eapply IHpath with (i := to_idx H4); eauto.
    - (* n, m > 0, use IH *)
      assert (n < m) by lia.
      assert (Hn' : n < length (v' :: pi))
        by (simpl in *; lia).
      assert (Hm' : m < length (v' :: pi))
        by (simpl in *; lia).
      assert (v0 = nth_safe (v' :: pi) (to_idx Hn')).
      { rewrite <- (nth_safe_cons Hn Hn'); auto. }
      assert (v'0 = nth_safe (v' :: pi) (to_idx Hm')).
      { rewrite <- (nth_safe_cons Hm Hm'); auto. }
      eapply IHpath; eauto.
  Qed.

End Accm.

(** * Measurement events *)

Section MeasEvt.

  (** [Cpy] semantics do not have measurement events. *)

  Lemma cpy_flow_no_meas :
    forall p ps e (v : io_evt (phrase_to_flow Cpy p ps e)),
      ~(meas_lbl (io_evt_lbl v)).
  Proof.
    unfold meas_lbl; simpl; intros; intro.
    destruct H as [p' [msr [q [tgt [ps' [e' H]]]]]].
    unfold io_evt_lbl in H.
    rewrite nth_safe_sngl in H.
    discriminate.
  Qed.

  (** [Sig] semantics do not have measurement events. *)

  Lemma sig_flow_no_meas :
    forall p ps e (v : io_evt (phrase_to_flow Sig p ps e)),
      ~(meas_lbl (io_evt_lbl v)).
  Proof.
    unfold meas_lbl; simpl; intros; intro.
    destruct H as [p' [msr [q [tgt [ps' [e' H]]]]]].
    unfold io_evt_lbl in H.
    rewrite nth_safe_sngl in H.
    discriminate.
  Qed.

  (** [Hsh] semantics do not have measurement events. *)

  Lemma hsh_flow_no_meas :
    forall p ps e (v : io_evt (phrase_to_flow Hsh p ps e)),
      ~(meas_lbl (io_evt_lbl v)).
  Proof.
    unfold meas_lbl; simpl; intros; intro.
    destruct H as [p' [msr [q [tgt [ps' [e' H]]]]]].
    unfold io_evt_lbl in H.
    rewrite nth_safe_sngl in H.
    discriminate.
  Qed.

  (** A measurement event in [At] phrase semantics belongs to the
      semantics of the body. *)

  Lemma at_flow_meas :
    forall t p p' q q' ps ps' e e' msr tgt
           (v : io_evt (phrase_to_flow (At q t) p ps e)),
      io_evt_lbl v = LMsp p' msr q' tgt ps' e' ->
      exists (v' : io_evt (phrase_to_flow t q (0 :: ps) e)),
        io_evt_lbl v' = io_evt_lbl v
        /\ v = app_rht [LReq p q e]
                 (app_lft [LRpy q p (phrase_to_evi t q (0 :: ps) e)] v').
  Proof.
    intros t p p' q q' ps ps' e e' msr tgt.
    rewrite at_phrase_to_flow. intros.
    rewrite at_io_evt_lbl in H.
    apply bf_cpy_cpy_evt_lbl_body;
      intro; unfold io_evt_lbl in H0;
      rewrite H in H0; discriminate.
  Qed.

  (** A measurement event in [Br] semantics belongs to the semantics
      of one of the branch bodies. *)

  Lemma br_flow_meas :
    forall b s t1 t2 p p' q ps ps' e e' msr tgt
           (v : io_evt (phrase_to_flow (Br b s t1 t2) p ps e)),
      io_evt_lbl v = LMsp p' msr q tgt ps' e' ->
      (exists (v' : io_evt (phrase_to_flow t1 p (0 :: ps) (evi_lft s e))),
          io_evt_lbl v' = io_evt_lbl v
          /\ v = xsplc_lft
                   [LSplt p s e]
                   (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
                   (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
                   [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)]
                   (app_rht
                      [LSplt p s e]
                      (app_lft [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)] v')))
      \/ (exists (v' : io_evt (phrase_to_flow t2 p (1 :: ps) (evi_rht s e))),
             io_evt_lbl v' = io_evt_lbl v
             /\ v = xsplc_rht
                      [LSplt p s e]
                      (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
                      (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
                      [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)]
                      (app_rht
                         [LSplt p s e]
                         (app_lft [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)] v'))).
  Proof.
    intros b s t1 t2 p p' q ps ps' e e' msr tgt.
    rewrite br_phrase_to_flow. intros.
    rewrite br_io_evt_lbl in H.
    apply evt_lbl_splt_join_bodies;
      intro; unfold io_evt_lbl in H0;
      rewrite H in H0; discriminate.
  Qed.

  (** For jumping over the above base cases in proofs about
      measurement events. *)

  Ltac basejump v :=
    try (pose proof (cpy_flow_no_meas _ _ _ v));
    try (pose proof (sig_flow_no_meas _ _ _ v));
    try (pose proof (hsh_flow_no_meas _ _ _ v));
    try contradiction.

  (** A measurement event is either the output event or has a unique
      outgoing edge.

      This lemma is crucial for the proof of Theorem 19. *)

  Lemma phrase_to_flow_meas_out_edge :
    forall t p ps e (v : io_evt (phrase_to_flow t p ps e)),
      meas_lbl (io_evt_lbl v) ->
      v = io_output_evt (phrase_to_flow t p ps e)
      \/ exists v', io_uniq_edge_out (phrase_to_flow t p ps e) v v'.
  Proof.
    induction t; intros; basejump v.
    - (* Meas *)
      left. simpl in v.
      pose proof (io_sngl_evt v) as [_ H0]. auto.
    - (* At *)
      right. unfold meas_lbl in H.
      destruct H as [p' [msr [q [tgt [ps' [e' H]]]]]].
      pose proof (
          at_flow_meas t p0 p' p q ps ps' e e' msr tgt v H
        ) as [v' [H0 H0']].
      assert (meas_lbl (io_evt_lbl v'))
        by (exists p', msr, q, tgt, ps', e'; rewrite <- H; auto).
      apply IHt in H1 as [H1|[v'' H1]].
      + exists (
            app_rht
              [LReq p0 p e]
              (app_rht
                 (phrase_to_lbls t p (0 :: ps) e)
                 (io_input_evt
                    (io_sngl (LRpy p p0 (phrase_to_evi t p (0 :: ps) e)))))
          ).
        subst. rewrite at_phrase_to_flow.
        apply bf_cpy_uniq_edge_out_rht.
        apply bf_cpy_uniq_edge_out_lft_input.
        apply phrase_to_flow_well_formed.
      + exists (
            app_rht
              [LReq p0 p e]
              (app_lft [LRpy p p0 (phrase_to_evi t p (0 :: ps) e)] v'')
          ).
        subst v. rewrite at_phrase_to_flow.
        apply bf_cpy_uniq_edge_out_rht.
        apply bf_cpy_uniq_edge_out_lft; auto.
        apply phrase_to_flow_well_formed.
    - (* Ln *)
      simpl in v; destruct H as
        [p' [msr [q [tgt [ps' [e' H]]]]]].
      pose proof (evt_lbl_bf_cpy_full _ _ v) as
        [[v' [H0 H0']]|[v' [H0 H0']]];
        assert (meas_lbl (io_evt_lbl v'))
        by (exists p', msr, q, tgt, ps', e'; rewrite <- H; auto).
      + right. apply IHt1 in H1 as [H1|[v'' H1]]; subst; simpl.
        * exists (
              app_rht
                (phrase_to_lbls t1 p (0 :: ps) e)
                (io_input_evt (phrase_to_flow t2 p (1 :: ps) (phrase_to_evi t1 p (0 :: ps) e)))
            ).
          apply bf_cpy_uniq_edge_out_lft_input.
          apply phrase_to_flow_well_formed.
        * exists (
              app_lft
                (phrase_to_lbls t2 p (1 :: ps) (phrase_to_evi t1 p (0 :: ps) e))
                v''
            ).
          apply bf_cpy_uniq_edge_out_lft; auto.
          apply phrase_to_flow_well_formed.
      + apply IHt2 in H1 as [H1|[v'' H1]]; subst; simpl.
        * left. symmetry. apply bf_cpy_output_evt.
        * right.
          exists (app_rht (phrase_to_lbls t1 p (0 :: ps) e) v'').
          apply bf_cpy_uniq_edge_out_rht; auto.
    - (* Br *)
      right. unfold meas_lbl in H.
      destruct H as [p' [msr [q [tgt [ps' [e' H]]]]]].
      pose proof (
          br_flow_meas b s t1 t2 p p' q ps ps' e e' msr tgt v H
        ) as [[v' [H0 H0']]|[v' [H0 H0']]];
        assert (meas_lbl (io_evt_lbl v'))
        by (exists p', msr, q, tgt, ps', e'; rewrite <- H; auto).
      + apply IHt1 in H1 as [H1|[v'' H1]]; subst.
        * exists (
              xsplc_lft
                [LSplt p s e]
                (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
                (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
                [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)]
                (app_rht
                   [LSplt p s e]
                   (app_rht
                      (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
                      (io_input_evt (io_sngl (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e))))))
            ).
          rewrite br_phrase_to_flow.
          apply splt_join_output_uniq_edge_out_lft.
          apply phrase_to_flow_well_formed.
        * exists (
              xsplc_lft
                [LSplt p s e]
                (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
                (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
                [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)]
                (app_rht [LSplt p s e] (app_lft [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)] v''))
            ).
          rewrite br_phrase_to_flow.
          apply splt_join_uniq_edge_out_lft; auto.
          apply phrase_to_flow_well_formed.
      + apply IHt2 in H1 as [H1|[v'' H1]]; subst.
        * exists (
              xsplc_rht
                [LSplt p s e]
                (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
                (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
                [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)]
                (app_rht
                   [LSplt p s e]
                   (app_rht
                      (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
                      (io_input_evt (io_sngl (LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e))))))
            ).
          rewrite br_phrase_to_flow.
          apply splt_join_output_uniq_edge_out_rht.
          apply phrase_to_flow_well_formed.
        * exists (
              xsplc_rht
                [LSplt p s e]
                (phrase_to_lbls t1 p (0 :: ps) (evi_lft s e))
                (phrase_to_lbls t2 p (1 :: ps) (evi_rht s e))
                [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)]
                (app_rht [LSplt p s e] (app_lft [LJoin p b (phrase_to_evi (Br b s t1 t2) p ps e)] v''))
            ).
          rewrite br_phrase_to_flow.
          apply splt_join_uniq_edge_out_rht; auto.
          apply phrase_to_flow_well_formed.
  Qed.

  Section MeasFstLst.

    (** Asserts that the first event in a sequence is a measurement
        event. *)

    Definition meas_fst [L : lbls] (pi : evt_seq L) : Prop :=
      exists v, fst_elem pi v /\ meas_lbl (nth_safe L v).

    (** Asserts that the last event in a sequence is a measurement
        event. *)

    Definition meas_lst [L : lbls] (pi : evt_seq L) : Prop :=
      exists v, lst_elem pi v /\ meas_lbl (nth_safe L v).

    (** An event sequence is [meas_fst] iff its [rev] reverse is
        [meas_lst] (and vice versa). *)

    Lemma meas_fst_iff_meas_lst_rev :
      forall [L : lbls] (pi : evt_seq L), meas_fst pi <-> meas_lst (rev pi).
    Proof.
      unfold meas_fst, meas_lst.
      split; intros [v [H H']];
        exists v; split;
        try apply fst_lst_rev; auto.
    Qed.

    (** No empty path is [meas_fst]. *)

    Lemma meas_fst_non_nil : forall [L : lbls], ~(@meas_fst L []).
    Proof.
      intros. intro.
      destruct H as [v [H0 H1]].
      destruct H0 as [i _].
      destruct i; simpl in *; lia.
    Qed.

    (** If a singleton is [meas_lst], the single event is a measurement
        event. *)

    Lemma meas_lst_sngl :
      forall [L : lbls] (v : idx L), meas_lst [v] -> meas_lbl (nth_safe L v).
    Proof.
      unfold meas_lst; intros.
      destruct H as [v' [H H']].
      apply lst_elem_sngl in H.
      subst; auto.
    Qed.

    (** Analogue of the previous lemma for [meas_fst] *)

    Corollary meas_fst_sngl :
      forall [L : lbls] (v : idx L), meas_fst [v] -> meas_lbl (nth_safe L v).
    Proof.
      intros.
      apply meas_fst_iff_meas_lst_rev in H.
      simpl in H. apply meas_lst_sngl; auto.
    Qed.

    (** Prepending an event to a sequence does not affect [meas_lst]. *)

    Lemma meas_lst_cons :
      forall [L : lbls] (pi : evt_seq L) v, meas_lst pi -> meas_lst (v :: pi).
    Proof.
      unfold meas_lst; intros.
      destruct H as [v' [H H']].
      exists v'. split; auto.
      apply lst_elem_cons; auto.
    Qed.

    (** Appending an event to a sequence does not affect [meas_fst]. *)

    Lemma meas_fst_app :
      forall [L : lbls] (pi : evt_seq L) v, meas_fst pi -> meas_fst (pi ++ [v]).
    Proof.
      intros.
      apply meas_fst_iff_meas_lst_rev.
      rewrite rev_unit.
      apply meas_lst_cons.
      apply meas_fst_iff_meas_lst_rev; auto.
    Qed.

    (** Analogue of [meas_lst_cons] for reversed lists *)

    Corollary meas_fst_rev_cons :
      forall [L : lbls] (pi : evt_seq L) v,
        meas_fst (rev pi) -> meas_fst (rev (v :: pi)).
    Proof.
      intros.
      apply meas_fst_iff_meas_lst_rev.
      rewrite rev_involutive.
      apply meas_fst_iff_meas_lst_rev in H.
      rewrite rev_involutive in H.
      apply meas_lst_cons; auto.
    Qed.

    (** Assuming the path is not a singleton, removing an event from the
        beginning does not affect [meas_lst]. *)

    Lemma meas_lst_cons_conv :
      forall [L : lbls] (pi : evt_seq L) v,
        pi <> [] -> meas_lst (v :: pi) -> meas_lst pi.
    Proof.
      unfold meas_lst; intros.
      destruct H0 as [v' [H0 H0']].
      exists v'. split; auto.
      eapply lst_elem_cons_conv;
        auto; eassumption.
    Qed.

    Corollary meas_lst_cons_iff :
      forall [L : lbls] (pi : evt_seq L) v v',
        meas_lst (v' :: pi) <-> meas_lst (v :: v' :: pi).
    Proof.
      split; intros.
      - apply meas_lst_cons; auto.
      - eapply meas_lst_cons_conv.
        + apply cons_neq_nil.
        + eassumption.
    Qed.

    (** Analogue of [meas_lst_cons_conv] for [meas_fst] *)

    Lemma meas_fst_app_conv :
      forall [L : lbls] (pi : evt_seq L) v,
        pi <> [] -> meas_fst (pi ++ [v]) -> meas_fst pi.
    Proof.
      intros.
      apply meas_fst_iff_meas_lst_rev.
      apply meas_fst_iff_meas_lst_rev in H0.
      rewrite rev_unit in H0.
      eapply meas_lst_cons_conv; eauto.
      intro. apply nil_iff_rev_nil in H1.
      contradiction.
    Qed.

    Corollary meas_fst_app_iff :
      forall [L : lbls] (pi : evt_seq L) v v',
        meas_fst (pi ++ [v']) <-> meas_fst ((pi ++ [v']) ++ [v]).
    Proof.
      split; intros.
      - apply meas_fst_app; auto.
      - eapply meas_fst_app_conv.
        + apply app_neq_nil.
        + eassumption.
    Qed.

  End MeasFstLst.

End MeasEvt.
