(** A path is a sequence of events in a graph with the property that
    an edge joins each event to the one following it. *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import Coq.Arith.Compare_dec.
Require Import List ListSet Lia.
Import ListNotations.

Require Import Index Edge Graph Preamble Prefix.

Set Implicit Arguments.

(** * Basic definitions *)

Section PathDefn.

  Variable A : Type.
  Variable l : list A.
  Variable G : graph l.

  (** A sequence of events in a graph *)

  Definition evt_seq := list (idx l).

  (** Definition 6: a path is an [evt_seq] with the [path]
      property%\index{Definition 6: Path}% *)

  Inductive path : evt_seq -> Prop :=
  | path_sngl :
    forall (v : idx l), path [v]
  | path_edge :
    forall (pi : evt_seq) (v v' : idx l),
      path (v' :: pi) ->
      In (v, v') G ->
      path (v :: v' :: pi).

  (** Reasoning about paths is often easier when they grow forwards or
      flow backwards (towards smaller indices) along edges, unlike the
      definition of [path].  We therefore define two alternative path
      definitions below and subsequently prove equivalences among
      them. *)

  (** Constructs the same sequences as [path] but does so forwards
      (via append) rather than backwards. *)

  Inductive path_app : evt_seq -> Prop :=
  | path_app_sngl :
    forall (v : idx l), path_app [v]
  | path_app_edge :
    forall (pi : evt_seq) (v v' : idx l),
      path_app (pi ++ [v']) ->
      In (v', v) G ->
      path_app (pi ++ [v'] ++ [v]).

  (** Constructs the [rev] reverses of [path] sequences.  The head of
      a [rev_path] is the last list element, and these grow forwards
      (along edges) to the left. *)

  Inductive rev_path : evt_seq -> Prop :=
  | rev_path_sngl :
    forall (v : idx l), rev_path [v]
  | rev_path_edge :
    forall (pi : evt_seq) (v v' : idx l),
      rev_path (v' :: pi) ->
      In (v', v) G ->
      rev_path (v :: v' :: pi).

  (** ** Equivalence of path definitions *)

  (** A [path] can be extended forwards by append. *)

  Lemma path_step_app : forall (pi : evt_seq) (v v' : idx l),
      path (pi ++ [v']) ->
      In (v', v) G ->
      path (pi ++ [v'] ++ [v]).
  Proof.
    induction pi; intros; inv H.
    - constructor; auto. constructor.
    - symmetry in H3.
      apply app_eq_nil in H3 as [_ H3].
      discriminate.
    - rewrite <- app_comm_cons.
      rewrite app_assoc. rewrite <- H2.
      simpl. constructor; try assumption.
      rewrite app_comm_cons. rewrite H2 in *.
      rewrite <- app_assoc. apply IHpi; auto.
  Qed.

  (** A [path_app] can be extended backwards by [cons]. *)

  Lemma path_app_step_cons : forall (pi : evt_seq) (v v' : idx l),
      path_app (v' :: pi) ->
      In (v, v') G ->
      path_app (v :: v' :: pi).
  Proof.
    intros pi. pattern pi.
    apply rev_ind; intros; [inv H | inv H0].
    - replace [v; v'] with ([] ++ [v] ++ [v']); auto.
      constructor; try assumption.
      simpl; constructor; auto.
    - destruct pi0; injection H1 as H1;
        [ | apply app_eq_nil in H as [_ H]];
        discriminate.
    - symmetry in H4.
      apply app_eq_nil in H4 as [_ H4].
      discriminate.
    - rewrite app_comm_cons.
      replace [v'0; v0]
        with ([v'0] ++ [v0]) in *; auto.
      constructor; try assumption.
      rewrite app_assoc in H2.
      rewrite app_comm_cons in H2.
      apply app_inj_tail in H2 as [H2 _].
      rewrite <- app_comm_cons.
      rewrite H2 in *.
      apply H; assumption.
  Qed.

  (** An [evt_seq] is a [path_app] iff it is a [path]. *)

  Corollary path_app_iff_path : forall pi, path_app pi <-> path pi.
  Proof.
    split; intros;
      induction H;
      try (constructor; auto); [
        apply path_step_app |
        apply path_app_step_cons
      ]; assumption.
  Qed.

  (** An [evt_seq] is a [path_app] iff its [rev] reverse is a
      [rev_path]. *)

  Lemma path_app_iff_rev_path_rev : forall pi,
      path_app pi <-> rev_path (rev pi).
  Proof.
    split; intros.
    - induction H; simpl; try constructor; auto.
      rewrite distr_rev in *. simpl in *.
      apply rev_path_edge; assumption.
    - remember (rev pi) as pi' eqn:H0.
      pose proof rev_involutive pi as H1.
      rewrite <- H0 in H1. rewrite <- H1.
      clear H0 H1 pi.
      induction H; simpl; try constructor; auto.
      rewrite <- app_assoc. simpl.
      apply path_app_edge; simpl in *; auto.
  Qed.

  (** An [evt_seq] is a [path] iff its [rev] reverse is a [rev_path]. *)

  Corollary path_iff_rev_path_rev : forall pi,
      path pi <-> rev_path (rev pi).
  Proof.
    intros. rewrite <- path_app_iff_path.
    apply path_app_iff_rev_path_rev.
  Qed.

End PathDefn.

#[export]
  Hint Resolve path_sngl : core.
#[export]
  Hint Resolve path_app_sngl : core.
#[export]
  Hint Resolve rev_path_sngl : core.

Section PathLems.

  Variable A : Type.
  Variable l l1 l2 : list A.
  Variable G  : graph l.
  Variable G1 : graph l1.
  Variable G2 : graph l2.

  (** Paths can be joined whenever an edge permits it. *)

  Lemma path_join : forall pi pi' v v',
      path G (pi ++ [v]) ->
      path G (v' :: pi') ->
      In (v, v') G ->
      path G ((pi ++ [v]) ++ v' :: pi').
  Proof.
    induction pi; simpl; intros; [
      | destruct pi; simpl in *; inv H
      ]; constructor; auto.
  Qed.

  (** Every prefix of a path is a path. *)

  Lemma path_prfx : forall pi pi',
      path G pi -> prfx pi' pi -> path G pi'.
  Proof.
    intros.
    rewrite <- path_app_iff_path in *.
    induction H.
    - apply prfx_sngl in H0.
      subst. auto.
    - rewrite app_assoc in H0.
      apply prfx_app in H0.
      destruct H0.
      + apply IHpath_app; auto.
      + subst. rewrite <- app_assoc.
        constructor; auto.
  Qed.

  (** The next two results show that [disjoint_union] preserves the
      paths of its constituents. *)

  Lemma disjoint_union_path_lft : forall pi,
      path G1 pi -> path (disjoint_union G1 G2) (map (app_lft l2) pi).
  Proof.
    intros. induction H; simpl in *;
      try constructor;
      try apply disjoint_union_edge_lft;
      auto.
  Qed.

  Lemma disjoint_union_path_rht : forall pi,
      path G2 pi -> path (disjoint_union G1 G2) (map (@app_rht A l1 l2) pi).
  Proof.
    intros. induction H; simpl in *;
      try constructor;
      try apply disjoint_union_edge_rht;
      auto.
  Qed.

  (** A path through a disjoint union is a path through one of the
      constituents. *)

  Lemma disjoint_union_path : forall pi,
      path (disjoint_union G1 G2) pi ->
      (exists pi1, path G1 pi1 /\ pi = map (app_lft l2) pi1)
      \/ (exists pi2, path G2 pi2 /\ pi = map (@app_rht A l1 l2) pi2).
  Proof.
    intros. induction H.
    - (* Take cases on whether idx_nat v < length l1 *)
      destruct (
          le_le_S_dec (length l1) (idx_nat v)
        ) as [Hl|H]; [
          (* length l1 <= idx_nat v *)
          pose proof (app_idx_rht_bnd _ _ _ Hl) as H;
          pose proof ((app_idx_rht _ _ _ Hl) H); right |
          (* idx_nat v < length l1 *)
          pose proof (app_idx_lft _ _ _ H); left
        ]; exists [to_idx H]; split;
        try (apply path_sngl);
        try (rewrite map_cons; f_equal; auto).
    - (* Four cases on which graph the path and edge are from *)
      apply disjoint_union_edge in H0.
      destruct IHpath as [[pi1 [H1 H2]]|[pi2 [H1 H2]]];
        [destruct pi1 | destruct pi2];
        simpl in H2; try discriminate;
        injection H2 as H2 H2';
        destruct H0 as [
          [u [u' [H0 [H0' H0'']]]] |
          [u [u' [H0 [H0' H0'']]]]
        ]; rewrite H2 in H0'';
        (* Handles the two contradictory cases *)
        try (rewrite idx_eq_iff in H0'';
             destruct i, u'; simpl in H0''; lia);
        (* Handles the allowable cases *)
        try (apply app_lft_inj in H0'';  left; exists (u :: u' :: pi1));
        try (apply app_rht_inj in H0''; right; exists (u :: u' :: pi2));
        subst; split; try (apply path_edge);
        try (repeat rewrite map_cons); auto.
  Qed.

  (** A path remains a path when an additional edge is added to the
      graph. *)

  Lemma add_edge_path : forall v v' pi,
      path G pi -> path (edges_add (v, v') G) pi.
  Proof.
    intros. induction H;
      try constructor;
      try (apply set_add_intro; right);
      auto.
  Qed.

  (** Characterizes the paths through a disjoint union augmented with
      one additional edge connecting the first graph to the second. *)

  Lemma connected_disjoint_union_path : forall (v1 : evt G1) (v2 : evt G2) pi,
      path (edges_add (to_app_edge v1 v2) (disjoint_union G1 G2)) pi ->
      path (disjoint_union G1 G2) pi
      \/ (exists pi1 pi2,
             path G1 (pi1 ++ [v1]) /\ path G2 (v2 :: pi2)
             /\ pi = (map (app_lft l2) (pi1 ++ [v1]))
                       ++ (map (@app_rht A l1 l2) (v2 :: pi2))).
  Proof.
    intros. induction H;
      [ left; constructor | ].
    apply set_add_iff in H0.
    unfold to_app_edge in H0.
    destruct IHpath; destruct H0.
    - (* Paths starting with v1 into G2 *)
      right. exists []. simpl.
      injection H0 as H0. subst.
      (* Take cases on whether the rest of the path is in G1 or G2 *)
      apply disjoint_union_path in H1
          as [[[|v' pi'] [H0 H1]]|[[|v' pi'] [H0 H1]]];
        simpl in H1; try discriminate; injection H1 as H1.
      + (* Rest of path in G1 (contradiction) *)
        rewrite idx_eq_iff in H1.
        destruct v2, v'. simpl in H1. lia.
      + (* Rest of path in G2 *)
        apply app_rht_inj in H1. subst v' pi.
        exists pi'. intuition.
    - (* Path and edge within disjoint union *)
      left. constructor; auto.
    - (* Paths whose tail traverses both graphs but starts with v2
         (contradiction) *)
      injection H0 as H0. subst.
      destruct H1 as [pi1 [pi2 [H1 [H2 H3]]]].
      rewrite map_cons, map_app in H3.
      destruct pi1 as [| v' pi1'];
        simpl in H3; injection H3 as H3;
        rewrite idx_eq_iff in H3;
        destruct v2; [destruct v1 | destruct v'];
        simpl in H3; lia.
    - (* Paths where (v1, v2) is in the disjoint union that traverse
         both graphs *)
      destruct H1 as [pi1 [pi2 [H1 [H2 H3]]]].
      rewrite map_cons, map_app in H3.
      (* Take cases on whether (v1, v2) is in G1 or G2 *)
      apply disjoint_union_edge in H0 as [
            [u [u' [H0 [H0' H0'']]]] |
            [u [u' [H0 [H0' H0'']]]]
          ]; subst; simpl in H3.
      + (* Edge in G1 *)
        right. destruct pi1 as [| u'' pi1'];
          simpl in H3; injection H3 as H3;
          apply app_lft_inj in H3; subst u' pi;
          [exists [u] | exists (u :: u'' :: pi1'); rewrite map_app];
          exists pi2; simpl; intuition; constructor; auto.
      + (* Edge in G2 (contradiction) *)
        destruct pi1 as [| u'' pi1'];
          simpl in H3; injection H3 as H3;
          rewrite idx_eq_iff in H3; destruct u';
          [destruct v1 | destruct u''];
          simpl in H3; lia.
  Qed.

  (** If an event has a unique outgoing edge, any path starting at
      that event with length greater than 1 immediately traverses that
      edge. *)

  Lemma path_uniq_edge_out :
    forall pi v v' (H : 1 < length pi),
      path G pi ->
      fst_elem pi v ->
      uniq_edge_out G v v' ->
      nth_safe pi (to_idx H) = v'.
  Proof.
    intros. inv H0; try (simpl in *; lia).
    destruct H1 as [i [H1 H1']].
    rewrite (to_idx_nat_evi i) in *.
    destruct i as [n Hn].
    simpl in H1. subst n.
    simpl in H1'. subst v0.
    apply H2 in H4. subst.
    reflexivity.
  Qed.

End PathLems.

(** * Paths through IO graphs *)

Section IOPathDefn.

  Variable A : Type.
  Variable l : list A.
  Variable G : io_graph l.

  (** A path through an [io_graph] is a path through its underlying
      [graph]. *)

  Definition io_path pi := path (io_to_graph G) pi.

  (** The analogue of [path_app] for [io_graph] *)

  Definition io_path_app pi := path_app (io_to_graph G) pi.

  (** The analogue of [rev_path] for [io_graph] *)

  Definition io_rev_path pi := rev_path (io_to_graph G) pi.

  (** The next three lemmas lift the equivalences among [path],
      [path_app] and [rev_path] to their [io_graph] analogues. *)

  Lemma io_path_app_iff_path :
    forall pi, io_path_app pi <-> io_path pi.
  Proof.
    unfold io_path_app, io_path.
    destruct G. simpl. intros.
    apply path_app_iff_path.
  Qed.

  Lemma io_path_app_iff_rev_path_rev :
    forall pi, io_path_app pi <-> io_rev_path (rev pi).
  Proof.
    unfold io_path_app, io_rev_path.
    destruct G. simpl. intros.
    apply path_app_iff_rev_path_rev.
  Qed.

  Lemma io_path_iff_rev_path_rev :
    forall pi, io_path pi <-> io_rev_path (rev pi).
  Proof.
    intros.
    rewrite <- io_path_app_iff_path.
    apply io_path_app_iff_rev_path_rev.
  Qed.

  (** Lifts [path_prfx] to [io_path]. *)

  Lemma io_path_prfx : forall pi pi',
      io_path pi -> prfx pi' pi -> io_path pi'.
  Proof.
    apply path_prfx.
  Qed.

  (** Lifts [path_uniq_edge_out] to [io_path]. *)

  Lemma io_path_uniq_edge_out :
    forall pi v v' (H : 1 < length pi),
      io_path pi ->
      fst_elem pi v ->
      io_uniq_edge_out G v v' ->
      nth_safe pi (to_idx H) = v'.
  Proof.
    apply path_uniq_edge_out.
  Qed.

End IOPathDefn.

(** * Paths through Before Nil and Before Copy *)

Section BfNilCpyPath.

  Variable A : Type.
  Variable l1 l2 l3 l4 : list A.

  (** The next two results show that Before Nil preserves the paths of
      its constituents. *)

  Lemma bf_nil_path_lft : forall (G1 : io_graph l1) (G2 : io_graph l2) pi,
      io_path G1 pi -> io_path (bf_nil G1 G2) (map (app_lft l2) pi).
  Proof.
    unfold io_path.
    destruct G1, G2. simpl. intros.
    apply disjoint_union_path_lft; auto.
  Qed.

  Lemma bf_nil_path_rht : forall (G1 : io_graph l1) (G2 : io_graph l2) pi,
      io_path G2 pi -> io_path (bf_nil G1 G2) (map (@app_rht A l1 l2) pi).
  Proof.
    unfold io_path.
    destruct G1, G2. simpl. intros.
    apply disjoint_union_path_rht; auto.
  Qed.

  (** A Before Nil path is a path through one of the constituents. *)

  Lemma bf_nil_path : forall (G1 : io_graph l1) (G2 : io_graph l2) pi,
      io_path (bf_nil G1 G2) pi ->
      (exists pi1, io_path G1 pi1 /\ pi = map (app_lft l2) pi1)
      \/ (exists pi2, io_path G2 pi2 /\ pi = map (@app_rht A l1 l2) pi2).
  Proof.
    unfold io_path.
    destruct G1, G2. simpl. intros.
    apply disjoint_union_path; auto.
  Qed.

  (** The next two results show that Before Copy also preserves the
      paths of its constituents. *)

  Lemma bf_cpy_path_lft : forall (G1 : io_graph l1) (G2 : io_graph l2) pi,
      io_path G1 pi -> io_path (bf_cpy G1 G2) (map (app_lft l2) pi).
  Proof.
    unfold io_path.
    destruct G1, G2. simpl. intros.
    apply add_edge_path.
    apply disjoint_union_path_lft; auto.
  Qed.

  Lemma bf_cpy_path_rht : forall (G1 : io_graph l1) (G2 : io_graph l2) pi,
      io_path G2 pi -> io_path (bf_cpy G1 G2) (map (@app_rht A l1 l2) pi).
  Proof.
    unfold io_path.
    destruct G1, G2. simpl. intros.
    apply add_edge_path.
    apply disjoint_union_path_rht; auto.
  Qed.

  (** A Before Copy path is a path through one of the constituents or
      passes from the first graph into the second via the additional
      edge. *)

  Lemma bf_cpy_path : forall (G1 : io_graph l1) (G2 : io_graph l2) pi,
      io_path (bf_cpy G1 G2) pi ->
      (exists pi1, io_path G1 pi1 /\ pi = map (app_lft l2) pi1)
      \/ (exists pi2, io_path G2 pi2 /\ pi = map (@app_rht A l1 l2) pi2)
      \/ (exists pi1 pi2,
             io_path G1 (pi1 ++ [io_output_evt G1])
             /\ io_path G2 (io_input_evt G2 :: pi2)
             /\ pi = (map (app_lft l2) (pi1 ++ [io_output_evt G1]))
                       ++ (map (@app_rht A l1 l2) (io_input_evt G2 :: pi2))).
  Proof.
    unfold io_path.
    destruct G1, G2. simpl. intros.
    apply connected_disjoint_union_path in H.
    destruct H; [
        apply disjoint_union_path in H;
        destruct H |
      ]; repeat (try (left; assumption); right);
      assumption.
  Qed.

  (** A path through the Before Nil is a path through the Before Copy. *)

  Lemma bf_nil_cpy_path : forall (G1 : io_graph l1) (G2 : io_graph l2) pi,
      io_path (bf_nil G1 G2) pi -> io_path (bf_cpy G1 G2) pi.
  Proof.
    intros. induction H; [
      | apply bf_nil_cpy_edge in H0
      ]; constructor; auto.
  Qed.

  Lemma path_bf_cpy_bf_nil : forall (G1 : io_graph l1) (G2 : io_graph l2) pi,
      io_path (bf_cpy G1 G2) pi <->
        io_path (bf_nil G1 G2) pi
        \/ (exists pi1 pi2,
                io_path G1 (pi1 ++ [io_output_evt G1])
                /\ io_path G2 (io_input_evt G2 :: pi2)
                /\ pi = (map (app_lft l2) (pi1 ++ [io_output_evt G1]))
                          ++ (map (@app_rht A l1 l2)
                                (io_input_evt G2 :: pi2))).
  Proof.
    intros.
    split; intro.
    - apply bf_cpy_path in H.
      destruct H.
      + left.
        repeat destruct_ex_and.
        subst.
        apply bf_nil_path_lft; auto.
      + destruct H.
        * left.
          repeat destruct_ex_and.
          subst.
          apply bf_nil_path_rht; auto.
        * right.
          repeat destruct_ex_and.
          subst.
          exists x.
          exists x0.
          simpl.
          split; auto.
    - destruct H.
      + apply bf_nil_cpy_path; auto.
      + repeat destruct_ex_and. subst.
        rewrite map_app.
        rewrite map_cons.
        apply path_join.
        * apply (@bf_cpy_path_lft _ G2) in H.
          rewrite map_app in H; auto.
        * apply (bf_cpy_path_rht G1) in H0.
          rewrite map_cons in H0; auto.
        * apply bf_cpy_edge_add.
  Qed.

End BfNilCpyPath.

(** * Paths through Split-Join *)

Section SplitJoinPath.

  Variable A : Type.

  (** A [splt_join_lft] has a path iff the mirrored [splt_join_rht]
      has the same path. *)

  Lemma splt_join_lft_rht_path_mirr :
    forall [l : list A]
           (s : splt)
           (ai : A) (G : io_graph l) (ao : A)
           pi,
      io_path (splt_join_lft s ai G ao) pi <->
        io_path (splt_join_rht (splt_mirr s) ai G ao) pi.
  Proof.
    intros. rewrite splt_join_lft_rht_mirr_eq. reflexivity.
  Qed.

  (** A [splt_join] has a path iff its mirror image has the mirrored
      path. *)

  Lemma splt_join_path_mirr :
    forall [l1 l2 : list A]
           (s : splt)
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
           pi,
      io_path (splt_join s ai G1 G2 ao) pi <->
        io_path (splt_join (splt_mirr s) ai G2 G1 ao) (map (iswp [ai] l1 l2 [ao]) pi).
  Proof.
    split; intros;
      [ | rewrite <- iswp_inv_map];
      induction H;
      try apply splt_join_edge_mirr in H0;
      try rewrite splt_mirr_inv in H0;
      repeat rewrite map_cons;
      constructor; auto.
  Qed.

  (** A path through a [splt_join_lft Nil] is a path through
      [splt_join_lft s] for all [s]. *)

  Lemma splt_join_lft_nil_path :
    forall [l : list A]
           (s : splt) (ai : A) (G : io_graph l) (ao : A) pi,
      io_path (splt_join_lft Nil ai G ao) pi ->
      io_path (splt_join_lft s ai G ao) pi.
  Proof.
    unfold splt_join_lft.
    destruct s; intros;
      try (apply bf_nil_cpy_path); auto.
  Qed.

  (** A path through a [splt_join_rht Nil] is a path through
      [splt_join_rht s] for all [s]. *)

  Lemma splt_join_rht_nil_path :
    forall [l : list A]
           (s : splt) (ai : A) (G : io_graph l) (ao : A) pi,
      io_path (splt_join_rht Nil ai G ao) pi ->
      io_path (splt_join_rht s ai G ao) pi.
  Proof.
    unfold splt_join_rht.
    destruct s; intros;
      try (apply bf_nil_cpy_path); auto.
  Qed.

  (** Every path through a [splt_join Nil] is a path through the
      corresponding [splt_join Lft] and [splt_join Rht]. *)

  Lemma splt_join_nil_lft_rht_path :
    forall [l1 l2 : list A]
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A) pi,
      io_path (splt_join Nil ai G1 G2 ao) pi ->
      io_path (splt_join Lft ai G1 G2 ao) pi
      /\ io_path (splt_join Rht ai G1 G2 ao) pi.
  Proof.
    intros. induction H; [
      | destruct IHpath as [IH0 IH1];
        apply splt_join_nil_lft_rht_edge in H0;
        destruct H0 as [H0 H1]
      ]; split; constructor; auto.
  Qed.

  (** Modulo translation, if a path through the left branch of a
      [splt_join Nil] has an initial event that also belongs to the
      right branch, then the path is a singleton. *)

  Lemma splt_join_lft_nil_path_from_rht :
    forall [l1 l2 : list A]
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
           u pi v v',
      io_path (splt_join_lft Nil ai G1 ao) (u :: pi) ->
      In (v, v') (io_to_graph (splt_join_rht Nil ai G2 ao)) ->
      xsplc_lft [ai] l1 l2 [ao] u = xsplc_rht [ai] l1 l2 [ao] v' ->
      pi = [].
  Proof.
    unfold splt_join_lft, splt_join_rht. intros.
    pose proof (
        splt_join_rht_nil_edge_to_lft G1 G2 ao u v v' H0 H1
      ) as [H2 [H2' H2'']].
    clear H0 H1. subst.
    destruct pi; try reflexivity.
    apply bf_nil_path in H
        as [[pi' [H H']]|[pi' [H H']]];
      destruct pi' as [| v pi'];
      try discriminate;
      injection H' as H';
      destruct pi';
      try discriminate;
      injection H0 as H0;
      try (inv H; simpl in *; contradiction).
    apply bf_cpy_path in H as
        [[pi'' [H2 H2']] |
          [[pi'' [H2 H2']] |
            [pi1' [pi2' [H2 [H2' H2'']]]]]];
      try (destruct pi'' as [|v' pi'']; try discriminate);
      try (destruct pi''; try discriminate).
    - injection H2' as H2'. subst. idx_neq H' v'.
    - inversion H2; simpl in *; contradiction.
    - repeat rewrite map_app in H2''.
      repeat rewrite map_cons in H2''.
      destruct pi1' as [| v'' pi'']; simpl in *;
        injection H2'' as H2''; subst;
        try (idx_neq H' v'');
        try (idx_neq H' (io_output_evt G1)).
  Qed.

  (** Analogue of the previous result for the right-left symmetric
      case *)

  Lemma splt_join_rht_nil_path_from_lft :
    forall [l1 l2 : list A]
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
           u pi v v',
      io_path (splt_join_rht Nil ai G2 ao) (u :: pi) ->
      In (v, v') (io_to_graph (splt_join_lft Nil ai G1 ao)) ->
      xsplc_rht [ai] l1 l2 [ao] u = xsplc_lft [ai] l1 l2 [ao] v' ->
      pi = [].
  Proof.
    intros.
    replace Nil with (splt_mirr Nil) in H; auto.
    rewrite <- splt_join_lft_rht_path_mirr in H.
    apply splt_join_lft_rht_edge_mirr in H0.
    unfold splt_mirr in H0.
    rewrite xsplc_lft_iswp_rht in H1.
    rewrite xsplc_rht_iswp_lft in H1.
    apply iswp_inj in H1.
    eapply splt_join_lft_nil_path_from_rht;
      eassumption.
  Qed.

  (* A helper for base case of [splt_join_nil_path] *)

  Ltac sjnp_base :=
    split; try constructor;
    rewrite map_cons; f_equal; rewrite idx_eq_iff;
    try rewrite idx_nat_xsplc_lft_lft;
    try rewrite idx_nat_xsplc_rht_rht;
    try (repeat rewrite idx_nat_app_lft);
    try (repeat rewrite idx_nat_app_rht);
    simpl in *; lia.

  (** A path through a [splt_join Nil] is a path through its left or
      right branch. *)

  Lemma splt_join_nil_path :
    forall [l1 l2 : list A]
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A) pi,
      io_path (splt_join Nil ai G1 G2 ao) pi ->
      (exists pi', io_path (splt_join_lft Nil ai G1 ao) pi' /\ pi = map (xsplc_lft [ai] l1 l2 [ao]) pi')
      \/ (exists pi', io_path (splt_join_rht Nil ai G2 ao) pi' /\ pi = map (xsplc_rht [ai] l1 l2 [ao]) pi').
  Proof.
    intros. induction H.
    - (* Take cases on where v is in the list *)
      pose proof (app4_idx_nat_range _ _ _ _ v).
      destruct H as [H|[[H0 H1]|[[H0 H1]|[H0 H1]]]].
      + left. exists [app_lft (l1 ++ [ao]) (to_idx H)]. sjnp_base.
      + left. assert (idx_nat v - length [ai] < length l1) by lia.
        exists [app_rht [ai] (app_lft [ao] (to_idx H))]. sjnp_base.
      + right. assert (
            idx_nat v - length [ai] - length l1 < length l2
          ) by lia.
        exists [app_rht [ai] (app_lft [ao] (to_idx H))]. sjnp_base.
      + right. assert (
            idx_nat v - length [ai] - length l1 - length l2 < length [ao]
          ) by lia.
        exists [app_rht [ai] (app_rht l2 (to_idx H))]. sjnp_base.
    - (* Take cases on where the path and edge are *)
      apply splt_join_edge in H0.
      destruct IHpath as [[pi' [IH0 IH1]]|[pi' [IH0 IH1]]];
        destruct H0 as [[u [u' [H0 [H1 H2]]]]|[u [u' [H0 [H1 H2]]]]].
      + (* Path and edge left *)
        list_eq IH1 pi'.
        apply (xsplc_lft_inj _ _ _ _ u' i) in IH1.
        left. exists (u :: u' :: pi'). subst.
        split; try constructor; auto.
      + (* Path left, edge right *)
        list_eq IH1 pi'. symmetry in IH1.
        pose proof (
            splt_join_lft_nil_path_from_rht G1 G2 ao u u' IH0 H0 IH1
          ). subst.
        pose proof (
            splt_join_rht_nil_edge_to_lft G1 G2 ao i u u' H0 IH1
          ) as [H1 [H1' H1'']]. subst.
        right. exists (
            map
              (@app_rht A [ai] (l2 ++ [ao]))
              [app_lft [ao] (io_output_evt G2);
               app_rht l2 (io_input_evt (io_sngl ao))]
          ).
        split; auto. unfold splt_join_rht.
        apply bf_nil_path_rht.
        constructor; auto.
        apply bf_cpy_edge_add.
      + (* Path right, edge left *)
        list_eq IH1 pi'. symmetry in IH1.
        pose proof (
            splt_join_rht_nil_path_from_lft G1 G2 ao u u' IH0 H0 IH1
          ). subst.
        pose proof (
            splt_join_lft_nil_edge_to_rht G1 G2 ao i u u' H0 IH1
          ) as [H1 [H1' H1'']]. subst.
        left. exists (
            map
              (@app_rht A [ai] (l1 ++ [ao]))
              [app_lft [ao] (io_output_evt G1);
               app_rht l1 (io_input_evt (io_sngl ao))]
          ).
        split; auto. unfold splt_join_lft.
        apply bf_nil_path_rht.
        constructor; auto.
        apply bf_cpy_edge_add.
      + list_eq IH1 pi'.
        apply (xsplc_rht_inj _ _ _ _ u' i) in IH1.
        right. exists (u :: u' :: pi'). subst.
        split; try constructor; auto.
  Qed.

  (** Every path through a [splt_join Lft] is a path through the
      corresponding [splt_join Nil] or traverses the additional left
      edge of [splt_join Lft] (and therefore belongs to the left
      branch). *)

  Lemma splt_join_lft_path :
    forall [l1 l2 : list A]
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A) pi,
      io_path (splt_join Lft ai G1 G2 ao) pi ->
      io_path (splt_join Nil ai G1 G2 ao) pi
      \/ (exists pi',
             io_path
               (splt_join_lft Lft ai G1 ao)
               ((app_lft (l1 ++ [ao]) (io_output_evt (io_sngl ai)))
                  :: (app_rht [ai] (io_input_evt (bf_cpy G1 (io_sngl ao))))
                  :: pi')
             /\ pi = map
                       (xsplc_lft [ai] l1 l2 [ao])
                       ((app_lft (l1 ++ [ao]) (io_output_evt (io_sngl ai)))
                          :: (app_rht [ai] (io_input_evt (bf_cpy G1 (io_sngl ao))))
                          :: pi')).
  Proof.
    intros. induction H;
      [left; constructor | ].
    apply splt_join_lft_edge in H0.
    destruct H0 as [H0|[H0 H0']];
      destruct IHpath as [H1|[pi' [H1 H1']]].
    - (* Path and edge in splt_join Nil *)
      left. constructor; auto.
    - (* Implied edge through input evt singleton graph
         (contradiction) *)
      rewrite map_cons in H1'.
      injection H1' as H1'.
      assert (
          v' = xsplc_lft
                 [ai] l1 l2 [ao]
                 (app_lft (l1 ++ [ao]) (io_output_evt (io_sngl ai)))
        ) by auto. clear H1'.
      apply splt_join_edge with (s := Nil) in H0.
      unfold splt_join_lft, splt_join_rht in H0.
      destruct H0 as [
          [u [u' [H0 [H0' H0'']]]] |
          [u [u' [H0 [H0' H0'']]]]];
        apply bf_nil_edge in H0;
        destruct H0 as [
          [x [x' [H4 [H4' H4'']]]] |
          [x [x' [H4 [H4' H4'']]]]];
        try (simpl in *; contradiction); subst.
      + apply xsplc_lft_inj in H3.
        idx_neq H3 (io_output_evt (io_sngl ai)).
      + symmetry in H3.
        apply xsplc_lft_eq_rht in H3.
        destruct H3 as [[j [H2 H2']]|[j [H2 H2']]]; [
            idx_neq H2' j |
            idx_neq H2 (io_output_evt (io_sngl ai))
          ].
    - (* Path through splt_join Nil, edge connects input evt to rest
         of left branch *)
      apply splt_join_nil_path in H1.
      destruct H1 as [[pi' [H1 H1']]|[pi' [H1 H1']]].
      + (* Path in the left branch *)
        list_eq H1' pi'.
        apply bf_nil_path in H1.
        destruct H1 as [
            [pi'' [H2' H2'']] |
            [pi'' [H2' H2'']]];
          list_eq H2'' pi''.
        * inv H2'; try (simpl in *; contradiction).
          apply (xsplc_lft_inj [ai] l1 l2 [ao]) in H1'.
          idx_neq H1' i0.
        * apply (xsplc_lft_inj [ai] l1 l2 [ao]) in H1'.
          apply app_rht_inj in H1'. subst.
          apply bf_cpy_path_rht with (G1 := io_sngl ai) in H2'.
          right. exists (
              map (@app_rht A [ai] (l1 ++ [ao])) pi''
            ).
          intuition. constructor; auto.
          apply bf_cpy_edge_add.
      + (* Path in the right branch (contradiction) *)
        list_eq H1' pi'.
        apply (xsplc_lft_eq_rht [ai] l1 l2 [ao]) in H1'.
        destruct H1' as
          [ [j [H1' H1'']] |
            [j [H1' H1'']] ];
          subst; [idx_neq H1' j | ].
        apply app_rht_inj in H1'.
        destruct G1; simpl in H1'.
        idx_neq H1' vi.
    - (* Implies output evt of initial singleton equals input event of
         rest of left branch (contradiction) *)
      rewrite map_cons in H1'.
      injection H1' as H1'.
      assert (
          v' = xsplc_lft
                 [ai] l1 l2 [ao]
                 (app_lft (l1 ++ [ao]) (io_output_evt (io_sngl ai)))
        ) by auto. clear H1'; subst.
      apply xsplc_lft_inj in H3.
      idx_neq H3 (io_output_evt (io_sngl ai)).
  Qed.

  (** Every path through a [splt_join Rht] is a path through the
      corresponding [splt_join Nil] or traverses the additional right
      edge of [splt_join Rht] (and therefore belongs to the right
      branch). *)

  Lemma splt_join_rht_path :
    forall [l1 l2 : list A]
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A) pi,
      io_path (splt_join Rht ai G1 G2 ao) pi ->
      io_path (splt_join Nil ai G1 G2 ao) pi
      \/ (exists pi',
             io_path
               (splt_join_rht Rht ai G2 ao)
               ((app_lft (l2 ++ [ao]) (io_output_evt (io_sngl ai)))
                  :: (app_rht [ai] (io_input_evt (bf_cpy G2 (io_sngl ao))))
                  :: pi')
             /\ pi = map
                       (xsplc_rht [ai] l1 l2 [ao])
                       ((app_lft (l2 ++ [ao]) (io_output_evt (io_sngl ai)))
                          :: (app_rht [ai] (io_input_evt (bf_cpy G2 (io_sngl ao))))
                          :: pi')).
  Proof.
    intros. apply splt_join_path_mirr in H.
    unfold splt_mirr in H.
    apply splt_join_lft_path in H.
    destruct H as [H|[pi' [H H']]].
    - left.
      apply splt_join_path_mirr in H.
      unfold splt_mirr in H.
      rewrite iswp_inv_map in H. auto.
    - right. exists pi'. split.
      + rewrite splt_join_lft_rht_path_mirr in H.
        unfold splt_mirr in H. auto.
      + apply iswp_eq_xsplc_lft_map. auto.
  Qed.

  (** Proof of the "path left, edge right" case of
      [splt_join_dup_path]. *)

  Lemma splt_join_dup_path_lft :
    forall [l1 l2 : list A]
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A) pi v v',
      io_path (splt_join Lft ai G1 G2 ao) (v' :: pi) ->
      In (v, v') (io_to_graph (splt_join Rht ai G1 G2 ao)) ->
      io_path (splt_join Lft ai G1 G2 ao) (v :: v' :: pi)
      \/ io_path (splt_join Rht ai G1 G2 ao) (v :: v' :: pi).
  Proof.
    intros.
    apply splt_join_rht_edge in H0.
    destruct H0 as [H0|[H0 H0']].
    + apply
        splt_join_nil_lft_rht_edge
        in H0 as [H0 _].
      left. constructor; auto.
    + apply splt_join_lft_path in H.
      destruct H as [H|[pi' [H H']]].
      * right. apply
          splt_join_nil_lft_rht_path
          in H as [_ H].
        subst. constructor; auto.
        apply splt_join_edge_rht.
        apply bf_cpy_edge_add.
      * rewrite map_cons in H'.
        injection H' as H'.
        assert (
            v' = xsplc_lft
                   [ai] l1 l2 [ao]
                   (app_lft (l1 ++ [ao]) (io_output_evt (io_sngl ai)))
          ) by auto.
        clear H'; subst; symmetry in H2.
        apply xsplc_lft_eq_rht in H2
            as [[j [H2 H2']]|[j [H2 H2']]]; [
            idx_neq H2' j |
            idx_neq H2 (io_output_evt (io_sngl ai))
          ].
  Qed.

  (** Every path through a [splt_join Dup] is a path through the
      corresponding [splt_join Lft] or [splt_join Rht]. *)

  Lemma splt_join_dup_path :
    forall [l1 l2 : list A]
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A) pi,
      io_path (splt_join Dup ai G1 G2 ao) pi ->
      io_path (splt_join Lft ai G1 G2 ao) pi \/ io_path (splt_join Rht ai G1 G2 ao) pi.
  Proof.
    intros. induction H;
      [ left; constructor | ].
    apply splt_join_dup_edge in H0.
    (* Discharge easy cases here *)
    destruct IHpath; destruct H0; [
        left; constructor |
        apply splt_join_dup_path_lft | |
        right; constructor
      ]; auto.
    (* Make symmetry argument for remaining case *)
    apply splt_join_path_mirr in H1.
    apply splt_join_edge_mirr in H0.
    unfold splt_mirr in H0, H1.
    rewrite map_cons in H1.
    pose proof (
        splt_join_dup_path_lft (iswp [ai] l1 l2 [ao] v) H1 H0
      ).
    destruct H2;
      apply splt_join_path_mirr in H2;
      repeat rewrite map_cons in H2;
      repeat rewrite iswp_inv in H2;
      rewrite iswp_inv_map in H2;
      intuition.
  Qed.

  (** A path through a Split-Join is a path through its left or right branch. *)

  Lemma splt_join_path :
    forall [l1 l2 : list A]
           (s : splt)
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
           pi,
      io_path (splt_join s ai G1 G2 ao) pi ->
      (exists pi', io_path (splt_join_lft s ai G1 ao) pi' /\ pi = map (xsplc_lft [ai] l1 l2 [ao]) pi')
      \/ (exists pi', io_path (splt_join_rht s ai G2 ao) pi' /\ pi = map (xsplc_rht [ai] l1 l2 [ao]) pi').
  Proof.
    intros. destruct s; [
        (* Reduce Dup to Lft \/ Rht *)
        apply splt_join_dup_path in H;
        destruct H |..
      ];
      (* Nil already proved *)
      try (apply splt_join_nil_path; auto);
      try (apply splt_join_lft_path
          in H as [H'|[pi' [H' H'']]]);
      try (apply splt_join_rht_path
          in H as [H'|[pi' [H' H'']]]);
      try (left; eexists; split; eassumption);
      try (right; eexists; split; eassumption);
      apply splt_join_nil_path in H'
        as [[pi' [H' H'']]|[pi' [H' H'']]]; [
        apply (splt_join_lft_nil_path Dup) in H' |
        apply (splt_join_rht_nil_path Dup) in H' |
        apply (splt_join_lft_nil_path Dup) in H' |
        apply (splt_join_rht_nil_path Dup) in H' |
        apply (splt_join_lft_nil_path Lft) in H' |
        apply (splt_join_rht_nil_path Lft) in H' |
        apply (splt_join_lft_nil_path Rht) in H' |
        apply (splt_join_rht_nil_path Rht) in H'
      ];
      try (left; eexists; split; eassumption);
      try (right; eexists; split; eassumption).
  Qed.

End SplitJoinPath.

(** * Graph acyclicity *)

Section Acyclic.

  Variable A : Type.

  (** Asserts that an event sequence is acyclic: no events repeat. *)

  Definition acyclic_evt_seq [l : list A] (pi : evt_seq l) : Prop :=
    forall i j,
      nth_safe pi i = nth_safe pi j ->
      i = j.

  (** An empty event sequence is acyclic. *)

  Lemma acyclic_evt_seq_empty : forall [l : list A], @acyclic_evt_seq l [].
  Proof.
    unfold acyclic_evt_seq. intros.
    destruct i; simpl in *; lia.
  Qed.

  (** A singleton event sequence is acyclic. *)

  Definition acyclic_evt_seq_sngl : forall [l : list A] (v : idx l),
      acyclic_evt_seq [v].
  Proof.
    unfold acyclic_evt_seq. intros.
    rewrite idx_eq_iff.
    rewrite (idx_sngl i).
    rewrite (idx_sngl j).
    reflexivity.
  Qed.

  (** Two acyclic event sequences may be appended to form another
      acyclic event sequence so long as they have no common element. *)

  Lemma acyclic_evt_seq_app : forall (l : list A) (l1 l2 : evt_seq l),
      acyclic_evt_seq l1 ->
      acyclic_evt_seq l2 ->
      (forall i j, nth_safe l1 i <> nth_safe l2 j) ->
      acyclic_evt_seq (l1 ++ l2).
  Proof.
    intros. unfold acyclic_evt_seq; intros.
    pose proof (e_nth_safe_app l1 l2 i).
    pose proof (e_nth_safe_app l1 l2 j).
    destruct H3 as [[i' [H3 H3']]|[i' [H3 H3']]];
      destruct H4 as [[j' [H4 H4']]|[j' [H4 H4']]];
      subst; rewrite H3 in H2; rewrite H4 in H2;
      try apply H in H2; try apply H0 in H2; subst;
      [ | | symmetry in H2 | ];
      try apply H1 in H2; try contradiction; auto.
  Qed.

  (** An event sequence is acyclic iff its reverse is. *)

  Lemma acyclic_evt_seq_rev :
    forall (l : list A) (pi : evt_seq l),
      acyclic_evt_seq pi <-> acyclic_evt_seq (rev pi).
  Proof.
    unfold acyclic_evt_seq; split; intros.
    - pose proof (rev_idx_preimage _ i) as [i' Hi'].
      pose proof (rev_idx_preimage _ j) as [j' Hj'].
      rewrite Hi' in H0; rewrite Hj' in H0.
      repeat rewrite nth_safe_rev in H0.
      apply H in H0; subst; reflexivity.
    - repeat rewrite <- (@nth_safe_rev _ pi) in H0.
      apply H in H0. rewrite rev_idx_eq_iff; auto.
  Qed.

  (** The [fst_elem] and [lst_elem] of an acyclic event sequence of
      length greater than 1 are different. *)

  Lemma acyclic_evt_seq_fst_neq_lst :
    forall (l : list A) (pi : evt_seq l) v v',
      acyclic_evt_seq pi ->
      fst_elem pi v ->
      lst_elem pi v' ->
      1 < length pi ->
      v <> v'.
  Proof.
    unfold fst_elem, lst_elem;
      intros; intro; subst.
    destruct H0 as [i [H0 H0']].
    destruct H1 as [j [H1 H1']].
    rewrite <- H1' in H0'.
    apply H in H0'.
    rewrite idx_eq_iff in H0'.
    rewrite H0, H1 in H0'. lia.
  Qed.

  (** Mapping an injective function over an acyclic event sequence
      preserves this property. *)

  Lemma acyclic_evt_seq_map_inj :
    forall (l1 l2 : list A) (f : idx l1 -> idx l2) (pi : evt_seq l1),
      inj f -> acyclic_evt_seq pi -> acyclic_evt_seq (map f pi).
  Proof.
    destruct pi as [|a pi]; intros;
      try apply acyclic_evt_seq_empty.
    unfold acyclic_evt_seq; intros.
    rewrite idx_eq_iff.
    rewrite (to_idx_nat_evi i) in H1.
    rewrite (to_idx_nat_evi j) in H1.
    destruct i as [n Hn].
    destruct j as [m Hm].
    unfold idx_nat, proj1_sig.
    unfold idx_evi, proj2_sig in H1.
    assert (H' : n < length (a :: pi) /\ m < length (a :: pi)).
    { split; rewrite <- map_length with (f := f); auto. }
    destruct H' as [Hn' Hm'].
    assert (idx_nat (to_idx Hn) = idx_nat (to_idx Hn')) by auto.
    assert (idx_nat (to_idx Hm) = idx_nat (to_idx Hm')) by auto.
    rewrite nth_safe_map with (i := to_idx Hn') in H1; auto.
    rewrite nth_safe_map with (i := to_idx Hm') in H1; auto.
    apply H in H1. apply H0 in H1.
    rewrite idx_eq_iff in H1; auto.
  Qed.

  (** The next four results show that [app_lft], [app_rht], [xsplc_lft]
      and [xsplc_rht] preserve acyclicity of event sequences. *)

  Corollary acyclic_app_lft : forall (l1 l2 : list A) (pi : evt_seq l1),
      acyclic_evt_seq pi -> acyclic_evt_seq (map (app_lft l2) pi).
  Proof.
    intros; apply acyclic_evt_seq_map_inj; auto; apply app_lft_inj.
  Qed.

  Corollary acyclic_app_rht : forall (l1 l2 : list A) (pi : evt_seq l2),
      acyclic_evt_seq pi -> acyclic_evt_seq (map (@app_rht A l1 l2) pi).
  Proof.
    intros; apply acyclic_evt_seq_map_inj; auto; apply app_rht_inj.
  Qed.

  Corollary acyclic_xsplc_lft :
    forall [l1 l2 l3 l4 : list A] (pi : evt_seq (l1 ++ l2 ++ l4)),
      acyclic_evt_seq pi -> acyclic_evt_seq (map (xsplc_lft l1 l2 l3 l4) pi).
  Proof.
    intros; apply acyclic_evt_seq_map_inj; auto; apply xsplc_lft_inj.
  Qed.

  Corollary acyclic_xsplc_rht :
    forall [l1 l2 l3 l4 : list A] (pi : evt_seq (l1 ++ l3 ++ l4)),
      acyclic_evt_seq pi -> acyclic_evt_seq (map (xsplc_rht l1 l2 l3 l4) pi).
  Proof.
    intros; apply acyclic_evt_seq_map_inj; auto; apply xsplc_rht_inj.
  Qed.

  (** Asserts that a graph is acyclic: every path through it is an
      acyclic event sequence. *)

  Definition acyclic [l : list A] (G : graph l) :=
    forall pi,
      path G pi -> acyclic_evt_seq pi.

  (** An equivalent definition of [acyclic] for [io_graph]. *)

  Definition io_acyclic [l : list A] (G : io_graph l) :=
    acyclic (io_to_graph G).

  (** An equivalent characterization of [io_acyclic] in terms of
      [io_path]. *)

  Lemma io_acyclic_paths : forall [l : list A] (G : io_graph l),
      io_acyclic G <-> forall pi, io_path G pi -> acyclic_evt_seq pi.
  Proof. intuition. Qed.

  (** Edge events in an acyclic graph are distinct. *)

  Lemma acyclic_edge_neq : forall [l : list A] (G : graph l) v v',
      acyclic G -> In (v, v') G -> v <> v'.
  Proof.
    intros.
    assert (path G [v; v']) by (constructor; auto).
    apply H in H1. intro; subst v'.
    assert (0 < length [v; v]) by (simpl; lia).
    assert (1 < length [v; v]) by (simpl; lia).
    assert (nth_safe [v; v] (to_idx H2) = v) by auto.
    assert (nth_safe [v; v] (to_idx H3) = v) by auto.
    rewrite <- H5 in H4.
    pose proof (H1 (to_idx H2) (to_idx H3) H4).
    rewrite idx_eq_iff in H6.
    simpl in H6. lia.
  Qed.

  (** Lifts the previous result to [io_graph]. *)

  Lemma io_acyclic_edge_neq : forall [l : list A] (G : io_graph l) v v',
      io_acyclic G -> In (v, v') (io_to_graph G) -> v <> v'.
  Proof.
    intros; apply (@acyclic_edge_neq _ (io_to_graph G)); auto.
  Qed.

  (** An empty graph is acyclic. *)

  Lemma acyclic_empty : forall [l : list A], acyclic (empty_edges l).
  Proof.
    unfold acyclic. intros.
    induction H;
      try (simpl in *; contradiction).
    apply acyclic_evt_seq_sngl.
  Qed.

  (** A singleton [io_graph] is acyclic. *)

  Lemma io_acyclic_sngl : forall (a : A), io_acyclic (io_sngl a).
  Proof.
    unfold io_acyclic. simpl.
    intros. apply acyclic_empty.
  Qed.

  (** The Before Nil of acyclic IO graphs is acyclic. *)

  Lemma bf_nil_acyclic :
    forall (l1 l2 : list A) (G1 : io_graph l1) (G2: io_graph l2),
      io_acyclic G1 ->
      io_acyclic G2 ->
      io_acyclic (bf_nil G1 G2).
  Proof.
    intros. rewrite io_acyclic_paths; intros.
    apply bf_nil_path in H1.
    destruct H1 as
      [ [pi' [H1 H1']] |
        [pi' [H1 H1']] ]; subst;
      try apply acyclic_app_lft;
      try apply acyclic_app_rht;
      try apply H in H1;
      try apply H0 in H1; auto.
  Qed.

  (** The Before Copy of acyclic IO graphs is acyclic. *)

  Lemma bf_cpy_acyclic :
    forall [l1 l2 : list A] (G1 : io_graph l1) (G2 : io_graph l2),
      io_acyclic G1 ->
      io_acyclic G2 ->
      io_acyclic (bf_cpy G1 G2).
  Proof.
    intros. rewrite io_acyclic_paths; intros.
    apply path_bf_cpy_bf_nil in H1.
    destruct H1.
    - pose proof bf_nil_acyclic as F.
      specialize (F l1 l2 G1 G2).
      unfold io_acyclic in F.
      unfold acyclic in F.
      apply F; auto.
    - (* Remains to show the separation property from
       [acyclic_evt_seq_app] for the third case *)
      destruct H1 as [pi1' [pi2' [H1 [H1' H1'']]]]; subst;
        apply acyclic_evt_seq_app;
        try apply acyclic_app_lft;
        try apply acyclic_app_rht;
        try apply H in H1;
        try apply H0 in H1;
        try apply H0 in H1'; auto.
      unfold not; intros.
      rewrite (to_idx_nat_evi i) in H2.
      rewrite (to_idx_nat_evi j) in H2.
      destruct i as [n Hn]; destruct j as [m Hm].
      unfold idx_evi, proj2_sig in H2.
      assert (Hn' : n < length (pi1' ++ [io_output_evt G1])).
      { clear H2; rewrite map_length in Hn; auto. }
      assert (Hm' : m < length (io_input_evt G2 :: pi2')).
      { clear H2; rewrite map_length in Hm; auto. }
      rewrite (nth_safe_map _ (to_idx Hn')) in H2; auto.
      rewrite (nth_safe_map _ (to_idx Hm')) in H2; auto.
      idx_neq H2 (nth_safe (pi1' ++ [io_output_evt G1]) (to_idx Hn')).
  Qed.

  (** The next two results show that the left and right branches of a
      Split-Join are acyclic assuming the contituent graph is. *)

  Lemma splt_join_lft_acyclic :
    forall [l : list A]
           (s : splt)
           (ai : A) (G : io_graph l) (ao : A),
      io_acyclic G -> io_acyclic (splt_join_lft s ai G ao).
  Proof.
    unfold splt_join_lft;
      destruct s; intros;
      try apply bf_cpy_acyclic;
      try apply bf_nil_acyclic;
      try apply io_acyclic_sngl;
      apply bf_cpy_acyclic; auto;
      apply io_acyclic_sngl.
  Qed.

  Lemma splt_join_rht_acyclic :
    forall [l : list A]
           (s : splt)
           (ai : A) (G : io_graph l) (ao : A),
      io_acyclic G -> io_acyclic (splt_join_rht s ai G ao).
  Proof.
    intros. rewrite io_acyclic_paths. intros.
    replace s with (splt_mirr (splt_mirr s)) in H0;
      try apply splt_mirr_inv.
    rewrite <- splt_join_lft_rht_path_mirr in H0.
    apply splt_join_lft_acyclic in H0; auto.
  Qed.

  (** A Split-Join is acyclic assuming its constituents are. *)

  Lemma splt_join_acyclic :
    forall [l1 l2 : list A]
           (s : splt)
           (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A),
      io_acyclic G1 ->
      io_acyclic G2 ->
      io_acyclic (splt_join s ai G1 G2 ao).
  Proof.
    intros. rewrite io_acyclic_paths. intros.
    apply splt_join_path in H1.
    destruct H1 as
      [ [pi' [H1 H1']] |
        [pi' [H1 H1']] ]; subst;
      try apply acyclic_xsplc_lft;
      try apply acyclic_xsplc_rht;
      try apply splt_join_lft_acyclic in H1;
      try apply splt_join_rht_acyclic in H1;
      auto.
  Qed.

End Acyclic.

Unset Implicit Arguments.
