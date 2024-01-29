(** A graph is a set of edges over a set of labeled events.  The
    labels may be of any type and are organized into a list, while the
    events themselves are indices into this list. *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import Lia List ListSet PeanoNat.
Import ListNotations.

Require Import Preamble Edge Index.

Set Implicit Arguments.

(** Attempts to derive a [lia]-identifiable contradiction from an
    assumed equality between indices. *)

Ltac idx_neq H i :=
  rewrite idx_eq_iff in H;
  try (repeat rewrite idx_nat_app_rht in H);
  try (repeat rewrite idx_nat_app_lft in H);
  destruct i; simpl in *; try lia.

(** * Basic definitions *)

Section GraphDefn.

  Variable A : Type.
  Variable l : list A.

  Definition graph := edges l.

  (** The events of [G] are the indices of [l]. *)

  Definition evt (G : graph) := idx l.

  (** Unique outgoing edge *)

  Definition uniq_edge_out (G : graph) v v' :=
    In (v, v') G /\ forall v'', In (v, v'') G -> v'' = v'.

End GraphDefn.

(** * Graph operations *)

Section GraphOps.

  Variable A : Type.
  Variable l1 l2 : list A.

  (** Compute the disjoint union of graphs with like label type. *)

  Definition disjoint_union (G1 : graph l1) (G2 : graph l2) : graph (l1 ++ l2) :=
    edges_union (edges_app_lft l2 G1) (edges_app_rht l1 G2).

  (** The next two results show that [disjoint_union] keeps the
      edges of its constituents. *)

  Lemma disjoint_union_edge_lft : forall (G1 : graph l1) (G2 : graph l2) (v v' : evt G1),
      In (v, v') G1 -> In (app_lft l2 v, app_lft l2 v') (disjoint_union G1 G2).
  Proof.
    intros. unfold disjoint_union, edges_union.
    rewrite set_union_iff. left.
    unfold edges_app_lft, edge_app_lft.
    replace (app_lft l2 v, app_lft l2 v')
      with (map_pair (app_lft l2) (v, v'));
      try reflexivity.
    apply in_map. assumption.
  Qed.

  Lemma disjoint_union_edge_rht : forall (G1 : graph l1) (G2 : graph l2) (v v' : evt G2),
      In (v, v') G2 -> In (app_rht l1 v, app_rht l1 v') (disjoint_union G1 G2).
  Proof.
    intros. unfold disjoint_union, edges_union.
    rewrite set_union_iff. right.
    unfold edges_app_rht, edge_app_rht.
    replace (app_rht l1 v, app_rht l1 v')
      with (map_pair (@app_rht A l1 l2) (v, v'));
      try reflexivity.
    apply in_map. assumption.
  Qed.

  (** An edge in a disjoint union is from one of the disjuncts. *)

  Lemma disjoint_union_edge : forall (G1 : graph l1) (G2 : graph l2) v v',
      In (v, v') (disjoint_union G1 G2) ->
      (exists v1 v1', In (v1, v1') G1 /\ v = app_lft l2 v1 /\ v' = app_lft l2 v1')
      \/ (exists v2 v2', In (v2, v2') G2 /\ v = app_rht l1 v2 /\ v' = app_rht l1 v2').
  Proof.
    unfold disjoint_union, edges_union.
    intros. rewrite set_union_iff in H.
    destruct H; [
        left; unfold edges_app_lft in H |
        right; unfold edges_app_rht in H
      ];
      rewrite in_map_iff in H;
      destruct H as [[u u'] [H0 H1]]; [
        unfold edges_app_lft in H0 |
        unfold edges_app_rht in H0
      ];
      apply expand_map_pair in H0 as [H0 H0'];
      exists u, u'; intuition.
  Qed.

  (** The next two results show disjoint union preserves unique
      outgoing edges. *)

  Lemma disjoint_union_uniq_edge_out_lft :
    forall (G1 : graph l1) (G2 : graph l2) v v',
      uniq_edge_out G1 v v' ->
      uniq_edge_out (disjoint_union G1 G2) (app_lft l2 v) (app_lft l2 v').
  Proof.
    unfold uniq_edge_out.
    intros G1 G2 v v' [H0 H0']. split.
    - apply disjoint_union_edge_lft; auto.
    - intros. apply disjoint_union_edge in H.
      destruct H as
        [ [u [u' [H [H' H'']]]] |
          [u [u' [H [H' H'']]]] ];
        subst.
      + apply app_lft_inj in H'. subst u.
        apply H0' in H. subst; reflexivity.
      + idx_neq H' v.
  Qed.

  Lemma disjoint_union_uniq_edge_out_rht :
    forall (G1 : graph l1) (G2 : graph l2) v v',
      uniq_edge_out G2 v v' ->
      uniq_edge_out (disjoint_union G1 G2) (app_rht l1 v) (app_rht l1 v').
  Proof.
    unfold uniq_edge_out.
    intros G1 G2 v v' [H0 H0']. split.
    - apply disjoint_union_edge_rht; auto.
    - intros. apply disjoint_union_edge in H.
      destruct H as
        [ [u [u' [H [H' H'']]]] |
          [u [u' [H [H' H'']]]] ];
        subst.
      + idx_neq H' u.
      + apply app_rht_inj in H'. subst u.
        apply H0' in H. subst; reflexivity.
  Qed.

End GraphOps.

(** * IO graphs *)

Section IOGraph.

  Variable A : Type.
  Variable l : list A.

  (** An [io_graph] is a [graph] with two distinguished events, an
      input event [vi] and an output event [vo]. *)

  Inductive io_graph : Type :=
  | IOG (vi vo : idx l) (G : edges l).

  (** An [io_graph] has the same events as its underlying [graph]. *)

  Definition io_evt (G : io_graph) := idx l.

  (** Project an [io_graph] to its input event, output event and
      underlying graph. *)

  Definition io_input_evt (G : io_graph) : io_evt G :=
    match G with
    | IOG vi _ _ => vi
    end.

  Definition io_output_evt (G : io_graph) : io_evt G :=
    match G with
    | IOG _ vo _ => vo
    end.

  Definition io_to_graph (G : io_graph) : graph l :=
    match G with
    | IOG _ _ G' => G'
    end.

  (** Look up the label of an event in an [io_graph]. *)

  Definition io_evt_lbl (G : io_graph) (v : io_evt G) : A := nth_safe l v.

  (** Lifts [uniq_edge_out] to [io_graph]. *)

  Definition io_uniq_edge_out (G : io_graph) v v' := uniq_edge_out (io_to_graph G) v v'.

  (** An IO graph is in-well-formed if its input event has no incoming
      edge. *)

  Definition io_graph_in_well_formed (G : io_graph) : Prop :=
    forall v1 v2,
      In (v1, v2) (io_to_graph G) -> v2 <> io_input_evt G.

  (** An IO graph is out-well-formed if its output event has no
      outgoing edge. *)

  Definition io_graph_out_well_formed (G : io_graph) : Prop :=
    forall v1 v2,
      In (v1, v2) (io_to_graph G) -> v1 <> io_output_evt G.

  (** An IO graph is well-formed if it is in- and out-well-formed *)

  Definition io_graph_well_formed (G : io_graph) : Prop :=
    io_graph_in_well_formed G /\ io_graph_out_well_formed G.

End IOGraph.

(** * IO graph operations *)

Section IOGraphOps.

  Variable A : Type.

  (** Construct a singleton [io_graph] with no edges and whose sole
      event has a given label. *)

  Definition io_sngl (a : A) : io_graph [a].
  Proof.
    pose proof (Nat.lt_0_succ 0) as H0.
    assert (H : length [a] = 1) by reflexivity.
    rewrite <- H in H0.
    apply (IOG (to_idx H0) (to_idx H0) (empty_edges [a])).
  Defined.

  (** A singleton graph has a single label to look up. *)

  Lemma io_sngl_evt_lbl :
    forall (a : A) (v : io_evt (io_sngl a)), io_evt_lbl v = a.
  Proof.
    apply nth_safe_sngl.
  Qed.

  (** The sole event of a singleton [io_graph] is both its input and
      output event. *)

  Lemma io_sngl_evt :
    forall (a : A) (v : io_evt (io_sngl a)),
      v = io_input_evt (io_sngl a) /\ v = io_output_evt (io_sngl a).
  Proof.
    intros.
    rewrite (to_idx_nat_evi (io_input_evt (io_sngl a))).
    rewrite (to_idx_nat_evi (io_output_evt (io_sngl a))).
    destruct (io_input_evt (io_sngl a)) as [k Hk].
    destruct (io_output_evt (io_sngl a)) as [m Hm].
    rewrite (to_idx_nat_evi v).
    destruct v as [n Hn]. simpl idx_evi.
    assert (k = 0) by (simpl in *; lia).
    assert (m = 0) by (simpl in *; lia).
    assert (n = 0) by (simpl in *; lia).
    subst. split; apply to_idx_eq.
  Qed.

  (** A singleton IO graph is well-formed. *)

  Lemma io_sngl_well_formed : forall (a : A), io_graph_well_formed (io_sngl a).
  Proof.
    split; intros; [
        unfold io_graph_in_well_formed |
        unfold io_graph_out_well_formed
      ]; intros; simpl in *; contradiction.
  Qed.

  (** ** Before Nil and Before Copy operations *)

  Section BfNilCpy.

    Variable l1 l2 : list A.

    (** Compute the Before Nil of IO graphs.

        Abstractly, the Before Nil of [G1] and [G2] is the IO graph
        with input event equal to that of [G1], output event equal to
        that of [G2], and is otherwise the disjoint union of [G1] and
        [G2].  This is also true here modulo the translations required
        to merge the two label mappings and keep the two [edges]
        disjoint. *)

    Definition bf_nil (G1 : io_graph l1) (G2 : io_graph l2) :
      io_graph (l1 ++ l2) :=
      match G1, G2 with
      | IOG vi1 _ G1', IOG _ vo2 G2' =>
          IOG (app_lft l2 vi1) (app_rht l1 vo2) (disjoint_union G1' G2')
      end.

    (** Compute the Before Copy of IO graphs.

        The Before Copy of [G1] and [G2] is identical to their Before
        Nil with one additional edge connecting the output event of
        [G1] to the input event of [G2]. *)

    Definition bf_cpy (G1 : io_graph l1) (G2 : io_graph l2) :
      io_graph (l1 ++ l2) :=
      match G1, G2 with
      | IOG vi1 vo1 G1', IOG vi2 vo2 G2' =>
          IOG (app_lft l2 vi1) (app_rht l1 vo2)
            (edges_add (to_app_edge vo1 vi2) (disjoint_union G1' G2'))
      end.

    (** The next four lemmas relate the events and labels of [bf_nil
        G1 G2] and [bf_cpy G1 G2] to those of [G1] and [G2].  The
        [full] versions include extra information about the underlying
        [idx] values of the events in question. *)

    Lemma evt_lbl_bf_nil_full :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v : io_evt (bf_nil G1 G2)),
        (exists (v1 : io_evt G1), io_evt_lbl v = io_evt_lbl v1
                                  /\ v = app_lft l2 v1)
        \/ (exists (v2 : io_evt G2), io_evt_lbl v = io_evt_lbl v2
                                     /\ v = app_rht l1 v2).
    Proof.
      intros. apply e_nth_safe_app.
    Qed.

    Lemma evt_lbl_bf_cpy_full :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v : io_evt (bf_cpy G1 G2)),
        (exists (v1 : io_evt G1), io_evt_lbl v = io_evt_lbl v1
                                  /\ v = app_lft l2 v1)
        \/ (exists (v2 : io_evt G2), io_evt_lbl v = io_evt_lbl v2
                                     /\ v = app_rht l1 v2).
    Proof.
      intros. apply e_nth_safe_app.
    Qed.

    Lemma evt_lbl_bf_nil :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v : io_evt (bf_nil G1 G2)),
        (exists (v1 : io_evt G1), io_evt_lbl v = io_evt_lbl v1)
        \/ (exists (v2 : io_evt G2), io_evt_lbl v = io_evt_lbl v2).
    Proof.
      intros.
      pose proof (
          evt_lbl_bf_nil_full G1 G2 v
        ) as [[v1 [H _]]|[v2 [H _]]];
        [left; exists v1 | right; exists v2];
        auto.
    Qed.

    Lemma evt_lbl_bf_cpy :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v : io_evt (bf_cpy G1 G2)),
        (exists (v1 : io_evt G1), io_evt_lbl v = io_evt_lbl v1)
        \/ (exists (v2 : io_evt G2), io_evt_lbl v = io_evt_lbl v2).
    Proof.
      intros.
      pose proof (
          evt_lbl_bf_cpy_full G1 G2 v
        ) as [[v1 [H _]]|[v2 [H _]]];
        [left; exists v1 | right; exists v2];
        auto.
    Qed.

    (** The next three lemmas are the analogues of [app_lft_nth_safe]
        and [app_rht_nth_safe] for [io_evt_lbl] and Before Nil and
        Before Copy. *)

    Lemma app_rht_evt_lbl_bf_nil :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v : io_evt G2),
        @io_evt_lbl _ _ (bf_nil G1 G2) (app_rht l1 v) = io_evt_lbl v.
    Proof.
      unfold io_evt_lbl; intros.
      apply app_rht_nth_safe.
    Qed.

    Lemma app_lft_evt_lbl_bf_cpy :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v : io_evt G1),
        @io_evt_lbl _ _ (bf_cpy G1 G2) (app_lft l2 v) = io_evt_lbl v.
    Proof.
      unfold io_evt_lbl; intros.
      apply app_lft_nth_safe.
    Qed.

    Lemma app_rht_evt_lbl_bf_cpy :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v : io_evt G2),
        @io_evt_lbl _ _ (bf_cpy G1 G2) (app_rht l1 v) = io_evt_lbl v.
    Proof.
      unfold io_evt_lbl; intros.
      apply app_rht_nth_safe.
    Qed.

    (** The next three lemmas characterize the input and output events
        of Before Nil and Before Copy in terms of those of their
        constituents. *)

    Lemma bf_cpy_input_evt : forall (G1 : io_graph l1) (G2 : io_graph l2),
        io_input_evt (bf_cpy G1 G2) = app_lft l2 (io_input_evt G1).
    Proof.
      destruct G1, G2; auto.
    Qed.

    Lemma bf_nil_output_evt : forall (G1 : io_graph l1) (G2 : io_graph l2),
        io_output_evt (bf_nil G1 G2) = app_rht l1 (io_output_evt G2).
    Proof.
      destruct G1, G2; auto.
    Qed.

    Lemma bf_cpy_output_evt : forall (G1 : io_graph l1) (G2 : io_graph l2),
        io_output_evt (bf_cpy G1 G2) = app_rht l1 (io_output_evt G2).
    Proof.
      destruct G1, G2; auto.
    Qed.

    (** The next three lemmas show that Before Nil and Before Copy
        keep the edges of their constituents. *)

    Lemma bf_nil_edge_rht :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v v' : io_evt G2),
        In (v, v') (io_to_graph G2) ->
        In (app_rht l1 v, app_rht l1 v') (io_to_graph (bf_nil G1 G2)).
    Proof.
      destruct G1, G2. simpl. intros.
      apply disjoint_union_edge_rht; auto.
    Qed.

    Lemma bf_cpy_edge_lft :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v v' : io_evt G1),
        In (v, v') (io_to_graph G1) ->
        In (app_lft l2 v, app_lft l2 v') (io_to_graph (bf_cpy G1 G2)).
    Proof.
      destruct G1, G2. simpl. intros.
      apply set_add_intro. right.
      apply disjoint_union_edge_lft; auto.
    Qed.

    Lemma bf_cpy_edge_rht :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v v' : io_evt G2),
        In (v, v') (io_to_graph G2) ->
        In (app_rht l1 v, app_rht l1 v') (io_to_graph (bf_cpy G1 G2)).
    Proof.
      destruct G1, G2. simpl. intros.
      apply set_add_intro. right.
      apply disjoint_union_edge_rht; auto.
    Qed.

    (** The Before Copy has its additional edge. *)

    Lemma bf_cpy_edge_add : forall (G1 : io_graph l1) (G2 : io_graph l2),
        In (app_lft l2 (io_output_evt G1), app_rht l1 (io_input_evt G2))
          (io_to_graph (bf_cpy G1 G2)).
    Proof.
      destruct G1, G2. simpl; unfold to_app_edge.
      apply set_add_intro. left; auto.
    Qed.

    (** The next two lemmas characterize the edges through the [graph]
        underlying a Before Nil or Before Copy. *)

    (** A Before Nil edge is an edge of one of the constituents. *)

    Lemma bf_nil_edge :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v v' : io_evt (bf_nil G1 G2)),
        In (v, v') (io_to_graph (bf_nil G1 G2)) ->
        (exists v1 v1', In (v1, v1') (io_to_graph G1)
                        /\ v = app_lft l2 v1
                        /\ v' = app_lft l2 v1')
        \/ (exists v2 v2', In (v2, v2') (io_to_graph G2)
                           /\ v = app_rht l1 v2
                           /\ v' = app_rht l1 v2').
    Proof.
      destruct G1, G2. simpl. intros.
      apply disjoint_union_edge. auto.
    Qed.

    (** A Before Copy edge is either the additional edge linking the
        output of the first graph to the input of the second or an
        edge of one of the constituents. *)

    Lemma bf_cpy_edge :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v v' : io_evt (bf_cpy G1 G2)),
        In (v, v') (io_to_graph (bf_cpy G1 G2)) ->
        (v = app_lft l2 (io_output_evt G1)
         /\ v' = app_rht l1 (io_input_evt G2))
        \/ (exists v1 v1', In (v1, v1') (io_to_graph G1)
                           /\ v = app_lft l2 v1
                           /\ v' = app_lft l2 v1')
        \/ (exists v2 v2', In (v2, v2') (io_to_graph G2)
                           /\ v = app_rht l1 v2
                           /\ v' = app_rht l1 v2').
    Proof with auto.
      destruct G1, G2. simpl. intros.
      apply set_add_elim in H.
      destruct H.
      - left. unfold to_app_edge in H.
        injection H as H H'...
      - right. apply disjoint_union_edge...
    Qed.

    (** Every edge of a Before Nil is also an edge of the
        corresponding Before Copy. *)

    Lemma bf_nil_cpy_edge :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v v' : io_evt (bf_nil G1 G2)),
        In (v, v') (io_to_graph (bf_nil G1 G2)) ->
        In (v, v') (io_to_graph (bf_cpy G1 G2)).
    Proof.
      destruct G1, G2. simpl. intros.
      apply set_add_intro. intuition.
    Qed.

    (** Relate edges in [bf_cpy] with ones in [bf_nil]. *)

    Lemma in_bf_cpy_bf_nil :
      forall (G1 : io_graph l1) (G2 : io_graph l2) (v1 v2 : idx(l1 ++ l2)),
        In (v1, v2) (io_to_graph (bf_cpy G1 G2)) <->
          (In (v1, v2) (io_to_graph (bf_nil G1 G2))
           \/ (v1, v2) = (to_app_edge (io_output_evt G1) (io_input_evt G2))).
    Proof.
      intros.
      destruct G1 as [v1i v1o G1].
      destruct G2 as [v2i v2o G2].
      simpl in *.
      unfold edges_add.
      split; intros.
      - apply set_add_iff in H.
        intuition.
      - apply set_add_iff.
        intuition.
    Qed.

    (** The next two lemmas show that Before Nil preserves unique
        outgoing edges. *)

    Lemma bf_nil_uniq_edge_out_lft :
      forall (G1 : io_graph l1) (G2 : io_graph l2) v v',
        io_uniq_edge_out G1 v v' ->
        io_uniq_edge_out (bf_nil G1 G2) (app_lft l2 v) (app_lft l2 v').
    Proof.
      unfold io_uniq_edge_out.
      destruct G1; destruct G2; simpl.
      apply disjoint_union_uniq_edge_out_lft.
    Qed.

    Lemma bf_nil_uniq_edge_out_rht :
      forall (G1 : io_graph l1) (G2 : io_graph l2) v v',
        io_uniq_edge_out G2 v v' ->
        io_uniq_edge_out (bf_nil G1 G2) (app_rht l1 v) (app_rht l1 v').
    Proof.
      unfold io_uniq_edge_out.
      destruct G1; destruct G2; simpl.
      apply disjoint_union_uniq_edge_out_rht.
    Qed.

    (** If the left graph is out-well-formed, then Before Copy
        preserves unique outgoing edges. *)

    Lemma bf_cpy_uniq_edge_out_lft :
      forall (G1 : io_graph l1) (G2 : io_graph l2) v v',
        io_graph_out_well_formed G1 ->
        io_uniq_edge_out G1 v v' ->
        io_uniq_edge_out (bf_cpy G1 G2) (app_lft l2 v) (app_lft l2 v').
    Proof.
      intros G1 G2 v v' H [H0 H0']. split.
      - apply bf_cpy_edge_lft; auto.
      - intros. apply in_bf_cpy_bf_nil in H1 as [H1|H1].
        + pose proof (bf_nil_uniq_edge_out_lft G2 (conj H0 H0')).
          destruct H2. apply H3; auto.
        + unfold to_app_edge in H1.
          injection H1 as H1.
          apply app_lft_inj in H1. subst v.
          apply H in H0. contradiction.
    Qed.

    (** Before Copy always preserves unique outgoing edges in the
        right graph. *)

    Lemma bf_cpy_uniq_edge_out_rht :
      forall (G1 : io_graph l1) (G2 : io_graph l2) v v',
        io_uniq_edge_out G2 v v' ->
        io_uniq_edge_out (bf_cpy G1 G2) (app_rht l1 v) (app_rht l1 v').
    Proof.
      intros G1 G2 v v' [H H']. split.
      - apply bf_cpy_edge_rht; auto.
      - intros. apply in_bf_cpy_bf_nil in H0 as [H0|H0].
        + pose proof (bf_nil_uniq_edge_out_rht G1 (conj H H')).
          destruct H1. apply H2; auto.
        + unfold to_app_edge in H0.
          injection H0 as H0.
          idx_neq H0 (io_output_evt G1).
    Qed.

    (** If the left graph is out-well-formed, the additional edge
        connecting the output event of the left graph to the input
        event of the right graph in a Before Copy is a unique outgoing
        edge. *)

    Lemma bf_cpy_uniq_edge_out_lft_input :
      forall (G1 : io_graph l1) (G2 : io_graph l2),
        io_graph_out_well_formed G1 ->
        io_uniq_edge_out
          (bf_cpy G1 G2) (app_lft l2 (io_output_evt G1))
          (app_rht l1 (io_input_evt G2)).
    Proof.
      unfold
        io_uniq_edge_out,
        io_graph_out_well_formed.
      split; try apply bf_cpy_edge_add.
      intros. apply bf_cpy_edge in H0.
      destruct H0 as
        [ [H0 H0'] |
          [ [u [u' [H0 [H0' H0'']]]] |
            [u [u' [H0 [H0' H0'']]]] ]];
        auto.
      - apply app_lft_inj in H0'. subst u.
        apply H in H0. contradiction.
      - assert (app_lft l2 (io_output_evt G1) = app_rht l1 u) by auto.
        idx_neq H1 (io_output_evt G1).
    Qed.

    (** The next few lemmas deal with the well-formedness of Before
        Nil and Before Copy. *)

    (** A Before Nil is in-well-formed when its left constituent is. *)

    Lemma bf_nil_in_well_formed :
      forall (G1 : io_graph l1) (G2 : io_graph l2),
        io_graph_in_well_formed G1 ->
        io_graph_in_well_formed (bf_nil G1 G2).
    Proof.
      intros G1 G2.
      unfold io_graph_in_well_formed.
      intros; intro.
      destruct G1 as [v1i v1o G1].
      destruct G2 as [v2i v2o G2].
      simpl in *.
      apply disjoint_union_edge in H0.
      destruct H0; repeat destruct_ex_and; subst.
      - apply app_lft_inj in H1. subst.
        apply H in H0; auto.
      - idx_neq H1 v1i.
    Qed.

    (** A Before Nil is out-well-formed when its right constituent is. *)

    Lemma bf_nil_out_well_formed :
      forall (G1 : io_graph l1) (G2 : io_graph l2),
        io_graph_out_well_formed G2 ->
        io_graph_out_well_formed (bf_nil G1 G2).
    Proof.
      intros G1 G2.
      unfold io_graph_out_well_formed.
      intros; intro.
      destruct G1 as [v1i v1o G1].
      destruct G2 as [v2i v2o G2].
      simpl in *.
      apply disjoint_union_edge in H0.
      destruct H0; repeat destruct_ex_and; subst.
      - idx_neq H1 x.
      - apply app_rht_inj in H1. subst.
        apply H in H0; auto.
    Qed.

    (** A Before Copy is in-well-formed if its left constituent is. *)

    Lemma bf_cpy_in_well_formed :
      forall (G1 : io_graph l1) (G2 : io_graph l2),
        io_graph_in_well_formed G1 ->
        io_graph_in_well_formed (bf_cpy G1 G2).
    Proof.
      intros G1 G2.
      pose proof bf_nil_in_well_formed as F.
      specialize (F G1 G2).
      unfold io_graph_in_well_formed in *.
      intros; intro.
      apply in_bf_cpy_bf_nil in H0.
      destruct H0.
      - apply F in H0; auto.
        destruct G1 as [v1i v1o G1].
        destruct G2 as [v2i v2o G2].
        simpl in *.
        intuition.
      - destruct G1 as [v1i v1o G1].
        destruct G2 as [v2i v2o G2].
        simpl in *.
        inv H1.
        injection H0 as H0.
        idx_neq H1 v1i.
    Qed.

    (** A Before Copy is out-well-formed if its right constituent is. *)

    Lemma bf_cpy_out_well_formed :
      forall (G1 : io_graph l1) (G2 : io_graph l2),
        io_graph_out_well_formed G2 ->
        io_graph_out_well_formed (bf_cpy G1 G2).
    Proof.
      intros G1 G2.
      pose proof bf_nil_out_well_formed as F.
      specialize (F G1 G2).
      unfold io_graph_out_well_formed in *.
      intros; intro.
      apply in_bf_cpy_bf_nil in H0.
      destruct H0.
      - apply F in H0; auto.
        destruct G1 as [v1i v1o G1].
        destruct G2 as [v2i v2o G2].
        simpl in *.
        intuition.
      - destruct G1 as [v1i v1o G1].
        destruct G2 as [v2i v2o G2].
        simpl in *.
        inv H1.
        injection H0 as H0.
        idx_neq H0 v1o.
    Qed.

    (** [bf_cpy] is well-formed if its inputs are. *)

    Lemma bf_cpy_well_formed :
      forall (G1 : io_graph l1) (G2 : io_graph l2),
        io_graph_well_formed G1 ->
        io_graph_well_formed G2 ->
        io_graph_well_formed (bf_cpy G1 G2).
    Proof.
      intros G1 G2.
      unfold io_graph_well_formed.
      intros.
      destruct H.
      destruct H0.
      split.
      - apply bf_cpy_in_well_formed; auto.
      - apply bf_cpy_out_well_formed; auto.
    Qed.

  End BfNilCpy.

  (** ** Req-Rpy and branch constructions *)

  Section ReqRpyBr.

    Variable l : list A.

    (** Since they are common in our use case, we extend select
        results about Before Nil and Before Copy events and edges to
        constructions of the form [bf_nil G1 (bf_cpy G2 G3)] and
        [bf_cpy G1 (bf_cpy G2 G3)], where [G1] and [G3] are singleton
        IO graphs. *)

    Lemma bf_nil_cpy_sngls_edge :
      forall (ai : A) (G : io_graph l) (ao : A) v v',
        In (v, v')
          (io_to_graph (bf_nil (io_sngl ai) (bf_cpy G (io_sngl ao)))) ->
        (exists u u',
            In (u, u') (io_to_graph G)
            /\ v = app_rht [ai] (app_lft [ao] u)
            /\ v' = app_rht [ai] (app_lft [ao] u'))
        \/ (v = app_rht [ai] (app_lft [ao] (io_output_evt G))
            /\ v' = app_rht [ai] (app_rht l (io_input_evt (io_sngl ao)))).
    Proof.
      intros. apply bf_nil_edge in H.
      destruct H as [
          [v1 [v1' [H [H' H'']]]] |
          [v1 [v1' [H [H' H'']]]] ];
        try (simpl in *; contradiction).
      apply bf_cpy_edge in H as [
            [H0 H0'] |
            [ [u [u' [H0 [H0' H0'']]]] |
              [u [u' [H0 [H0' H0'']]]]]]; subst;
        try (simpl in *; contradiction);
        [ | left; exists u, u']; intuition.
    Qed.

    Lemma bf_nil_cpy_sngls_edge' :
      forall (ai : A) (G : io_graph l) (ao : A) v v',
        In (v, v') (io_to_graph G) ->
        In
          (app_rht [ai] (app_lft [ao] v), app_rht [ai] (app_lft [ao] v'))
          (io_to_graph (bf_nil (io_sngl ai) (bf_cpy G (io_sngl ao)))).
    Proof.
      intros.
      apply bf_nil_edge_rht.
      apply bf_cpy_edge_lft.
      assumption.
    Qed.

    Lemma bf_cpy_cpy_sngls_edge :
      forall (ai : A) (G : io_graph l) (ao : A) v v',
        In (v, v')
          (io_to_graph (bf_cpy (io_sngl ai) (bf_cpy G (io_sngl ao)))) ->
        (v = app_lft (l ++ [ao]) (io_output_evt (io_sngl ai))
         /\ v' = app_rht [ai] (app_lft [ao] (io_input_evt G)))
        \/ (exists u u',
               In (u, u') (io_to_graph G)
               /\ v = app_rht [ai] (app_lft [ao] u)
               /\ v' = app_rht [ai] (app_lft [ao] u'))
        \/ (v = app_rht [ai] (app_lft [ao] (io_output_evt G))
            /\ v' = app_rht [ai] (app_rht l (io_input_evt (io_sngl ao)))).
    Proof.
      intros. apply in_bf_cpy_bf_nil in H.
      destruct H.
      - right. apply bf_nil_cpy_sngls_edge; auto.
      - left. unfold to_app_edge in H.
        injection H as H.
        rewrite bf_cpy_input_evt in H0.
        intuition.
    Qed.

    Lemma bf_cpy_cpy_sngls_edge' :
      forall (ai : A) (G : io_graph l) (ao : A) v v',
        In (v, v') (io_to_graph G) ->
        In
          (app_rht [ai] (app_lft [ao] v), app_rht [ai] (app_lft [ao] v'))
          (io_to_graph (bf_cpy (io_sngl ai) (bf_cpy G (io_sngl ao)))).
    Proof.
      intros.
      apply bf_cpy_edge_rht.
      apply bf_cpy_edge_lft.
      assumption.
    Qed.

    Lemma bf_cpy_cpy_evt_lbl_body :
      forall (ai : A) (G : io_graph l) (ao : A)
             (v : io_evt (bf_cpy (io_sngl ai) (bf_cpy G (io_sngl ao)))),
        io_evt_lbl v <> ai ->
        io_evt_lbl v <> ao ->
        exists (v' : io_evt G),
          io_evt_lbl v' = io_evt_lbl v /\ v = app_rht [ai] (app_lft [ao] v').
    Proof.
      intros.
      pose proof (evt_lbl_bf_cpy_full _ _ v).
      destruct H1 as [[v' [H1 H1']]|[v' [H1 H1']]].
      - rewrite io_sngl_evt_lbl in H1. contradiction.
      - pose proof (evt_lbl_bf_cpy_full _ _ v').
        destruct H2 as [[v'' [H2 H2']]|[v'' [H2 H2']]].
        + exists v''. split; [rewrite <- H2 | subst]; auto.
        + rewrite <- H1 in H2.
          rewrite io_sngl_evt_lbl in H2. contradiction.
    Qed.

  End ReqRpyBr.

  (** ** Split-Join operation *)

  Section SpltJoin.

    (** Specifies how the first IO graph should be joined to the left
        and right branches in a Split-Join operation, defined below. *)

    Inductive splt : Type :=
    | Dup
    | Lft
    | Rht
    | Nil.

    (** The "mirror image" of a splitting specification. *)

    Definition splt_mirr (s : splt) : splt :=
      match s with
      | Lft => Rht
      | Rht => Lft
      | _ => s
      end.

    Lemma splt_mirr_inv : forall s, splt_mirr (splt_mirr s) = s.
    Proof. destruct s; auto. Qed.

    (** Compute the left branch of a Split-Join. *)

    Definition splt_join_lft
      [l : list A]
      (s : splt)
      (ai : A) (G : io_graph l) (ao : A)
      : io_graph ([ai] ++ l ++ [ao]) :=
      match s with
      | Dup | Lft => bf_cpy (io_sngl ai) (bf_cpy G (io_sngl ao))
      | _ => bf_nil (io_sngl ai) (bf_cpy G (io_sngl ao))
      end.

    (** Compute the right branch of a Split-Join. *)

    Definition splt_join_rht
      [l : list A]
      (s : splt)
      (ai : A) (G : io_graph l) (ao : A)
      : io_graph ([ai] ++ l ++ [ao]) :=
      match s with
      | Dup | Rht => bf_cpy (io_sngl ai) (bf_cpy G (io_sngl ao))
      | _ => bf_nil (io_sngl ai) (bf_cpy G (io_sngl ao))
      end.

    (** Compute the Split-Join of IO graphs.

        Intuitively, the Split-Join of [G1] and [G2] is the union of
        the [splt_join_lft s] of [G1] and the [splt_join_rht s] of
        [G2] with common initial and final event labels [ai] and [ao].
        The input and output events of the Split-Join are events
        labeled by [ai] and [ao], respectively.

        Split-Join is a bespoke operation intended for defining
        Copland data flow semantics. *)

    Definition splt_join
      [l1 l2 : list A]
      (s : splt)
      (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
      : io_graph ([ai] ++ l1 ++ l2 ++ [ao]) :=
      IOG
        (app_lft (l1 ++ l2 ++ [ao]) (io_input_evt (io_sngl ai)))
        (app_rht [ai] (app_rht l1 (app_rht l2 (io_output_evt (io_sngl ao)))))
        (edges_union
           (edges_xsplc_lft [ai] l1 l2 [ao] (io_to_graph (splt_join_lft s ai G1 ao)))
           (edges_xsplc_rht [ai] l1 l2 [ao] (io_to_graph (splt_join_rht s ai G2 ao)))).

    (** The next two lemmas relate the events and labels of [splt_join
        s ai G1 G2 ao] to those of its left and right branches.  The
        [full] version includes extra information about the underlying
        [idx] values of the events in question. *)

    Lemma evt_lbl_splt_join_br_full :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v : io_evt (splt_join s ai G1 G2 ao)),
        (exists (vl : io_evt (splt_join_lft s ai G1 ao)),
            io_evt_lbl v = io_evt_lbl vl
            /\ v = xsplc_lft [ai] l1 l2 [ao] vl)
        \/ (exists (vr : io_evt (splt_join_rht s ai G2 ao)),
               io_evt_lbl v = io_evt_lbl vr
               /\ v = xsplc_rht [ai] l1 l2 [ao] vr).
    Proof.
      intros. apply e_nth_safe_xsplc.
    Qed.

    Lemma evt_lbl_splt_join_br :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v : io_evt (splt_join s ai G1 G2 ao)),
        (exists (vl : io_evt (splt_join_lft s ai G1 ao)),
            io_evt_lbl v = io_evt_lbl vl)
        \/ (exists (vr : io_evt (splt_join_rht s ai G2 ao)),
               io_evt_lbl v = io_evt_lbl vr).
    Proof.
      intros.
      pose proof (
          evt_lbl_splt_join_br_full v
        ) as [[vl [H _]]|[vr [H _]]];
        [left; exists vl | right; exists vr];
        auto.
    Qed.

    (** If a [splt_join] event has a label different from the initial
        and final labels, the event must belong to one of the branch
        bodies. *)

    Lemma evt_lbl_splt_join_bodies :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v : io_evt (splt_join s ai G1 G2 ao)),
        io_evt_lbl v <> ai ->
        io_evt_lbl v <> ao ->
        (exists (v' : io_evt G1),
            io_evt_lbl v' = io_evt_lbl v
            /\ v = xsplc_lft [ai] l1 l2 [ao]
                     (app_rht [ai] (app_lft [ao] v')))
        \/ (exists (v' : io_evt G2),
               io_evt_lbl v' = io_evt_lbl v
               /\ v = xsplc_rht [ai] l1 l2 [ao]
                        (app_rht [ai] (app_lft [ao] v'))).
    Proof.
      intros. pose proof (evt_lbl_splt_join_br_full v).
      destruct H1 as [[v' [H1 H1']]|[v' [H1 H1']]];
        assert (io_evt_lbl v' <> ai) by (rewrite <- H1; auto);
        assert (io_evt_lbl v' <> ao) by (rewrite <- H1; auto);
        [left | right]; destruct s;
        try unfold splt_join_lft in v';
        try unfold splt_join_rht in v';
        try (pose proof (bf_cpy_cpy_evt_lbl_body G1 v' H2 H3) as H4);
        try (pose proof (bf_nil_cpy_evt_lbl_body G1 v' H2 H3) as H4);
        try (pose proof (bf_cpy_cpy_evt_lbl_body G2 v' H2 H3) as H4);
        try (pose proof (bf_nil_cpy_evt_lbl_body G2 v' H2 H3) as H4);
        destruct H4 as [v'' [H4 H4']];
        exists v''; split; try rewrite H4; subst; auto.
    Qed.

    (** The next two lemmas clarify the relationship between the input
        and output events of a [splt_join] to those of its left and
        right branches. *)

    Lemma splt_join_input_evt :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A),
        io_input_evt (splt_join s ai G1 G2 ao) =
          xsplc_lft [ai] l1 l2 [ao] (io_input_evt (splt_join_lft s ai G1 ao))
        /\ io_input_evt (splt_join s ai G1 G2 ao) =
             xsplc_rht [ai] l1 l2 [ao] (io_input_evt (splt_join_rht s ai G2 ao)).
    Proof.
      split; intros;
        destruct G1, G2; simpl;
        destruct s; simpl;
        reflexivity.
    Qed.

    Lemma splt_join_output_evt :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A),
        io_output_evt (splt_join s ai G1 G2 ao) =
          xsplc_lft [ai] l1 l2 [ao]
            (io_output_evt (splt_join_lft s ai G1 ao))
        /\ io_output_evt (splt_join s ai G1 G2 ao) =
             xsplc_rht [ai] l1 l2 [ao]
               (io_output_evt (splt_join_rht s ai G2 ao)).
    Proof.
      intros.
      unfold
        splt_join,
        splt_join_lft,
        splt_join_rht,
        io_output_evt,
        bf_nil, bf_cpy in *.
      destruct (io_sngl ai), G1, G2, (io_sngl ao).
      split; destruct s; apply idx_eq_iff;
        try rewrite idx_nat_xsplc_lft_rht;
        try rewrite idx_nat_xsplc_rht_rht;
        repeat rewrite idx_nat_app_rht; lia.
    Qed.

    (** The following corollary combines [splt_join_output_evt] with
        the analogous result for Before Copy to express the Split-Join
        output event in terms of that of the [ao] singleton. *)

    Corollary splt_join_output_evt_full :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A),
        io_output_evt (splt_join s ai G1 G2 ao) =
          xsplc_lft [ai] l1 l2 [ao]
            (app_rht [ai] (app_rht l1 (io_output_evt (io_sngl ao))))
        /\ io_output_evt (splt_join s ai G1 G2 ao) =
             xsplc_rht [ai] l1 l2 [ao]
               (app_rht [ai] (app_rht l2 (io_output_evt (io_sngl ao)))).
    Proof.
      intros.
      pose proof (splt_join_output_evt s ai G1 G2 ao) as [H0 H1].
      split; [rewrite H0 | rewrite H1]; f_equal;
        [unfold splt_join_lft | unfold splt_join_rht];
        destruct s;
        try rewrite bf_cpy_output_evt;
        try rewrite bf_nil_output_evt;
        rewrite bf_cpy_output_evt; auto.
    Qed.

    (** Over the same constituents, the [splt_join_lft] is equal to
        the mirrored [splt_join_rht]. *)

    Lemma splt_join_lft_rht_mirr_eq :
      forall [l : list A]
             (s : splt)
             (ai : A) (G : io_graph l) (ao : A),
        splt_join_lft s ai G ao = splt_join_rht (splt_mirr s) ai G ao.
    Proof.
      destruct s; unfold splt_mirr; reflexivity.
    Qed.

    (** A [splt_join_lft] has an edge iff its mirrored [splt_join_rht]
        has the same edge. *)

    Lemma splt_join_lft_rht_edge_mirr :
      forall [l : list A]
             (s : splt)
             (ai : A) (G : io_graph l) (ao : A)
             (v v' : idx ([ai] ++ l ++ [ao])),
        In (v, v') (io_to_graph (splt_join_lft s ai G ao)) <->
          In (v, v') (io_to_graph (splt_join_rht (splt_mirr s) ai G ao)).
    Proof.
      intros. rewrite splt_join_lft_rht_mirr_eq. reflexivity.
    Qed.

    (** A [splt_join] has an edge iff its mirror image has the
        mirrored edge. *)

    Lemma splt_join_edge_mirr :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v v' : idx ([ai] ++ l1 ++ l2 ++ [ao])),
        In (v, v') (io_to_graph (splt_join s ai G1 G2 ao)) <->
          In
            (iswp [ai] l1 l2 [ao] v, iswp [ai] l1 l2 [ao] v')
            (io_to_graph (splt_join (splt_mirr s) ai G2 G1 ao)).
    Proof.
      unfold
        io_to_graph,
        splt_join,
        edges_union,
        splt_join_lft,
        splt_join_rht,
        edges_xsplc_lft,
        edges_xsplc_rht.
      split; intros;
        rewrite set_union_iff in *;
        destruct H;
        [right | left | right | left];
        apply in_map_iff in H;
        destruct H as [[u u'] [H H']];
        apply expand_map_pair in H as [H0 H1];
        apply in_map_iff; subst;
        exists (u, u'); split;
        try (unfold splt_mirr; destruct s; assumption);
        try unfold edge_xsplc_lft;
        try unfold edge_xsplc_rht;
        unfold map_pair, fst, snd;
        try (f_equal; apply xsplc_rht_iswp_lft);
        try (f_equal; apply xsplc_lft_iswp_rht); [
          rewrite xsplc_lft_iswp_rht in H0, H1 |
          rewrite xsplc_rht_iswp_lft in H0, H1
        ]; apply iswp_inj in H0, H1; subst; f_equal.
    Qed.

    (** The next two lemmas show that Split-Join keeps the edges of
        its left and right branches. *)

    Lemma splt_join_edge_lft :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v v' : io_evt (splt_join_lft s ai G1 ao)),
        In (v, v') (io_to_graph (splt_join_lft s ai G1 ao)) ->
        In (xsplc_lft [ai] l1 l2 [ao] v, xsplc_lft [ai] l1 l2 [ao] v')
          (io_to_graph (splt_join s ai G1 G2 ao)).
    Proof.
      unfold splt_join, edges_union; intros; simpl.
      rewrite set_union_iff. left.
      unfold edges_xsplc_lft.
      apply in_map
        with (f := edge_xsplc_lft [ai] l1 l2 [ao]) in H.
      auto.
    Qed.

    Lemma splt_join_edge_rht :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v v' : io_evt (splt_join_rht s ai G2 ao)),
        In (v, v') (io_to_graph (splt_join_rht s ai G2 ao)) ->
        In (xsplc_rht [ai] l1 l2 [ao] v, xsplc_rht [ai] l1 l2 [ao] v')
          (io_to_graph (splt_join s ai G1 G2 ao)).
    Proof.
      unfold splt_join, edges_union; intros; simpl.
      rewrite set_union_iff. right.
      unfold edges_xsplc_rht.
      apply in_map
        with (f := edge_xsplc_rht [ai] l1 l2 [ao]) in H.
      auto.
    Qed.

    (** An edge of a Split-Join is an edge of the left or right branch. *)

    Lemma splt_join_edge :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v v' : io_evt (splt_join s ai G1 G2 ao)),
        In (v, v') (io_to_graph (splt_join s ai G1 G2 ao)) ->
        (exists vl vl',
            In (vl, vl') (io_to_graph (splt_join_lft s ai G1 ao))
            /\ v = xsplc_lft [ai] l1 l2 [ao] vl
            /\ v' = xsplc_lft [ai] l1 l2 [ao] vl')
        \/ (exists vr vr',
               In (vr, vr') (io_to_graph (splt_join_rht s ai G2 ao))
               /\ v = xsplc_rht [ai] l1 l2 [ao] vr
               /\ v' = xsplc_rht [ai] l1 l2 [ao] vr').
    Proof.
      unfold splt_join. simpl. intros.
      unfold edges_union in H.
      rewrite set_union_iff in H.
      destruct H; [
          left; unfold edges_xsplc_lft in H |
          right; unfold edges_xsplc_rht in H
        ];
        rewrite in_map_iff in H;
        destruct H as [[u u'] [H H']];
        try unfold edge_xsplc_lft in H;
        try unfold edge_xsplc_rht in H;
        apply expand_map_pair in H;
        exists u, u'; intuition.
    Qed.

    (** Every edge of a [splt_join Nil] is an edge of the
        corresponding [splt_join Lft] and [splt_join Rht]. *)

    Lemma splt_join_nil_lft_rht_edge :
      forall [l1 l2 : list A]
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v v' : io_evt (splt_join Nil ai G1 G2 ao)),
        In (v, v') (io_to_graph (splt_join Nil ai G1 G2 ao)) ->
        In (v, v') (io_to_graph (splt_join Lft ai G1 G2 ao))
        /\ In (v, v') (io_to_graph (splt_join Rht ai G1 G2 ao)).
    Proof.
      unfold
        io_to_graph,
        splt_join,
        edges_union,
        splt_join_lft,
        splt_join_rht,
        edges_xsplc_lft,
        edges_xsplc_rht.
      intros. rewrite set_union_iff in H.
      destruct H; split;
        rewrite set_union_iff;
        [left | left | right | right];
        apply in_map_iff;
        apply in_map_iff in H;
        destruct H as [[u u'] [H H']];
        exists (u, u'); intuition;
        try (apply bf_nil_cpy_edge; auto).
    Qed.

    (** All but one edge (the additional one) of a [splt_join Lft] is
        also an edge of the corresponding [splt_join Nil]. *)

    Lemma splt_join_lft_edge :
      forall [l1 l2 : list A]
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v v' : io_evt (splt_join Lft ai G1 G2 ao)),
        In (v, v') (io_to_graph (splt_join Lft ai G1 G2 ao)) ->
        In (v, v') (io_to_graph (splt_join Nil ai G1 G2 ao))
        \/ (v = xsplc_lft [ai] l1 l2 [ao] (app_lft (l1 ++ [ao]) (io_output_evt (io_sngl ai)))
            /\ v' = xsplc_lft [ai] l1 l2 [ao] (app_rht [ai] (io_input_evt (bf_cpy G1 (io_sngl ao))))).
    Proof.
      unfold
        io_to_graph,
        splt_join,
        edges_union,
        edges_xsplc_lft,
        splt_join_lft.
      intros. apply set_union_iff in H.
      destruct H.
      - apply in_map_iff in H.
        destruct H as [[u u'] [H H']].
        apply expand_map_pair in H.
        destruct H. apply bf_cpy_edge in H'.
        destruct H' as [
            [H1 H1'] |
            [[v1 [v1' [H1 [H1' H1'']]]] |
              [v2 [v2' [H1 [H1' H1'']]]]]].
        + subst. intuition.
        + simpl in H1. contradiction.
        + left. apply set_union_iff.
          (* Either disjunct works *)
          left. subst. apply in_map_iff.
          exists (app_rht [ai] v2, app_rht [ai] v2').
          split; try apply bf_nil_edge_rht; auto.
      - left. apply set_union_iff. intuition.
    Qed.

    (** All but one edge (the additional one) of a [splt_join Rht] is
        also an edge of the corresponding [splt_join Nil]. *)

    Lemma splt_join_rht_edge :
      forall [l1 l2 : list A]
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v v' : io_evt (splt_join Rht ai G1 G2 ao)),
        In (v, v') (io_to_graph (splt_join Rht ai G1 G2 ao)) ->
        In (v, v') (io_to_graph (splt_join Nil ai G1 G2 ao))
        \/ (v = xsplc_rht [ai] l1 l2 [ao]
                  (app_lft (l2 ++ [ao]) (io_output_evt (io_sngl ai)))
            /\ v' = xsplc_rht [ai] l1 l2 [ao]
                      (app_rht [ai] (io_input_evt (bf_cpy G2 (io_sngl ao))))).
    Proof.
      intros. apply splt_join_edge_mirr in H.
      unfold splt_mirr in H.
      apply splt_join_lft_edge in H.
      destruct H as [H|[H H']].
      - left. apply splt_join_edge_mirr in H.
        repeat rewrite iswp_inv in H. auto.
      - right. apply iswp_eq_xsplc_lft in H, H'.
        intuition.
    Qed.

    (** Every edge of a [split_join Dup] is an edge of either the
        corresponding [splt_join Lft] or [splt_join Rht]. *)

    Lemma splt_join_dup_edge :
      forall [l1 l2 : list A]
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (v v' : io_evt (splt_join Dup ai G1 G2 ao)),
        In (v, v') (io_to_graph (splt_join Dup ai G1 G2 ao)) ->
        In (v, v') (io_to_graph (splt_join Lft ai G1 G2 ao))
        \/ In (v, v') (io_to_graph (splt_join Rht ai G1 G2 ao)).
    Proof.
      unfold io_to_graph,
        splt_join,
        edges_union,
        splt_join_lft,
        splt_join_rht.
      intros. apply set_union_iff in H.
      destruct H; [left | right];
        apply set_union_iff; intuition.
    Qed.

    (** Modulo translation, if [(v, v')] is an edge of the right
        branch of a [splt_join Nil] where also [v'] belongs to the
        left branch, then [v'] is the [ao] singleton and [v] is the
        output event of the right graph. *)

    Lemma splt_join_rht_nil_edge_to_lft :
      forall [l1 l2 : list A]
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (u : io_evt (splt_join_lft Nil ai G1 ao))
             (v v' : io_evt (splt_join_rht Nil ai G2 ao)),
        In (v, v') (io_to_graph (splt_join_rht Nil ai G2 ao)) ->
        xsplc_lft [ai] l1 l2 [ao] u = xsplc_rht [ai] l1 l2 [ao] v' ->
        u = app_rht [ai] (app_rht l1 (io_input_evt (io_sngl ao)))
        /\ v' = app_rht [ai] (app_rht l2 (io_input_evt (io_sngl ao)))
        /\ v = app_rht [ai] (app_lft [ao] (io_output_evt G2)).
    Proof.
      unfold splt_join_rht. intros.
      apply bf_nil_edge in H as [
            [v1 [v1' [H _]]] |
            [v2 [v2' [H [H' H'']]]]
          ]; try (simpl in *; contradiction). subst.
      (* Implies v' is in one of the singletons *)
      apply xsplc_lft_eq_rht in H0
          as [[j [H0 H0']]|[j [H0 H0']]]; subst.
      - (* In ai singleton (contradiction) *)
        idx_neq H0' j.
      - (* In ao singleton, take cases on edge *)
        apply bf_cpy_edge in H as [
              [H H'] | [
                [v1 [v1' [H [H' H'']]]] |
                [v1 [v1' [H [H' H'']]]]]
            ]; try (simpl in *; contradiction); subst.
        + (* Edge connects G2 to ao singleton *)
          repeat apply app_rht_inj in H0'.
          subst. intuition.
        + (* Edge in G2 (contradiction) *)
          idx_neq H0' v1'.
    Qed.

    (** Analogue of the previous lemma for the right-left symmetric
        case *)

    Lemma splt_join_lft_nil_edge_to_rht :
      forall [l1 l2 : list A]
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             (u : io_evt (splt_join_rht Nil ai G2 ao))
             (v v' : io_evt (splt_join_lft Nil ai G1 ao)),
        In (v, v') (io_to_graph (splt_join_lft Nil ai G1 ao)) ->
        xsplc_rht [ai] l1 l2 [ao] u = xsplc_lft [ai] l1 l2 [ao] v' ->
        u = app_rht [ai] (app_rht l2 (io_input_evt (io_sngl ao)))
        /\ v' = app_rht [ai] (app_rht l1 (io_input_evt (io_sngl ao)))
        /\ v = app_rht [ai] (app_lft [ao] (io_output_evt G1)).
    Proof.
      intros.
      apply splt_join_lft_rht_edge_mirr in H.
      unfold splt_mirr in H.
      rewrite xsplc_lft_iswp_rht in H0.
      rewrite xsplc_rht_iswp_lft in H0.
      apply iswp_inj in H0.
      apply splt_join_rht_nil_edge_to_lft; auto.
    Qed.

    (** The next few lemmas deal with the unique outgoing
        edge-preserving properties of [splt_join]. *)

    (** Unique outgoing edges in the body of the left branch are
        preserved by [splt_join]. *)

    Lemma splt_join_uniq_edge_out_lft :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             v v',
        io_graph_out_well_formed G1 ->
        io_uniq_edge_out G1 v v' ->
        io_uniq_edge_out
          (splt_join s ai G1 G2 ao)
          (xsplc_lft [ai] l1 l2 [ao] (app_rht [ai] (app_lft [ao] v)))
          (xsplc_lft [ai] l1 l2 [ao] (app_rht [ai] (app_lft [ao] v'))).
    Proof.
      intros; destruct H0 as [H0 H0']. split.
      - apply splt_join_edge_lft.
        unfold splt_join_lft; destruct s;
          try apply bf_cpy_cpy_sngls_edge';
          try apply bf_nil_cpy_sngls_edge'; auto.
      - intros. apply splt_join_edge in H1.
        destruct H1 as
          [ [u [u' [H1 [H1' H1'']]]] |
            [u [u' [H1 [H1' H1'']]]] ].
        + apply xsplc_lft_inj in H1'.
          unfold splt_join_lft in H1; destruct s;
            try (apply bf_cpy_cpy_sngls_edge in H1 as
                  [[H2 H2']|[[w [w' [H2 [H2' H2'']]]]|[H2 H2']]]);
            try (apply bf_nil_cpy_sngls_edge in H1 as
                  [[w [w' [H2 [H2' H2'']]]]|[H2 H2']]); subst;
            try (apply app_rht_inj in H1');
            try (apply app_lft_inj in H1'); subst;
            try (apply H in H0);
            try (apply H0' in H2); subst;
            try reflexivity;
            try contradiction;
            idx_neq H1' (io_output_evt (io_sngl ai)).
        + apply xsplc_lft_eq_rht in H1' as
              [[j [H2 H2']]|[j [H2 H2']]]; subst.
          * idx_neq H2 j.
          * idx_neq H2 v.
    Qed.

    (** Unique outgoing edges in the body of the right branch are
        preserved by [splt_join] *)

    Lemma splt_join_uniq_edge_out_rht :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A)
             v v',
        io_graph_out_well_formed G2 ->
        io_uniq_edge_out G2 v v' ->
        io_uniq_edge_out
          (splt_join s ai G1 G2 ao)
          (xsplc_rht [ai] l1 l2 [ao] (app_rht [ai] (app_lft [ao] v)))
          (xsplc_rht [ai] l1 l2 [ao] (app_rht [ai] (app_lft [ao] v'))).
    Proof.
      intros; destruct H0 as [H0 H0']. split.
      - apply splt_join_edge_rht.
        unfold splt_join_lft; destruct s;
          try apply bf_cpy_cpy_sngls_edge';
          try apply bf_nil_cpy_sngls_edge'; auto.
      - intros. apply splt_join_edge in H1.
        destruct H1 as
          [ [u [u' [H1 [H1' H1'']]]] |
            [u [u' [H1 [H1' H1'']]]] ].
        + symmetry in H1'.
          apply xsplc_lft_eq_rht in H1' as
              [[j [H2 H2']]|[j [H2 H2']]]; subst.
          * idx_neq H2' j.
          * idx_neq H2' v.
        + apply xsplc_rht_inj in H1'.
          unfold splt_join_rht in H1; destruct s;
            try (apply bf_cpy_cpy_sngls_edge in H1 as
                  [[H2 H2']|[[w [w' [H2 [H2' H2'']]]]|[H2 H2']]]);
            try (apply bf_nil_cpy_sngls_edge in H1 as
                  [[w [w' [H2 [H2' H2'']]]]|[H2 H2']]); subst;
            try (apply app_rht_inj in H1');
            try (apply app_lft_inj in H1'); subst;
            try (apply H in H0);
            try (apply H0' in H2); subst;
            try reflexivity;
            try contradiction;
            idx_neq H1' (io_output_evt (io_sngl ai)).
    Qed.

    (** If the body of the left branch is well-formed, the edge
        connecting its output event to the terminal event of a
        [splt_join] is a unique outgoing edge. *)

    Lemma splt_join_output_uniq_edge_out_lft :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A),
        io_graph_out_well_formed G1 ->
        io_uniq_edge_out
          (splt_join s ai G1 G2 ao)
          (xsplc_lft [ai] l1 l2 [ao] (app_rht [ai] (app_lft [ao] (io_output_evt G1))))
          (xsplc_lft [ai] l1 l2 [ao] (app_rht [ai] (app_rht l1 (io_input_evt (io_sngl ao))))).
    Proof.
      split.
      - apply splt_join_edge_lft.
        unfold splt_join_lft; destruct s;
          try apply bf_cpy_edge_rht;
          try apply bf_nil_edge_rht;
          apply bf_cpy_edge_add.
      - intros. apply splt_join_edge in H0.
        destruct H0 as
          [ [u [u' [H0 [H0' H0'']]]] |
            [u [u' [H0 [H0' H0'']]]] ].
        + apply xsplc_lft_inj in H0'.
          unfold splt_join_lft in H0; destruct s;
            try (apply bf_cpy_cpy_sngls_edge in H0 as
                  [[H1 H1']|[[w [w' [H1 [H1' H1'']]]]|[H1 H1']]]);
            try (apply bf_nil_cpy_sngls_edge in H0 as
                  [[w [w' [H1 [H1' H1'']]]]|[H1 H1']]); subst;
            try reflexivity;
            try apply app_rht_inj in H0';
            try apply app_lft_inj in H0'; subst;
            try apply H in H1;
            try contradiction;
            try idx_neq H0' (io_output_evt (io_sngl ai)).
        + apply xsplc_lft_eq_rht in H0' as
              [[j [H1 H1']]|[j [H1 H1']]]; subst.
          * idx_neq H1 j.
          * idx_neq H1 (io_output_evt G1).
    Qed.

    (** If the body of the right branch is well-formed, the edge
        connecting its output event to the terminal event of a
        [splt_join] is a unique outgoing edge. *)

    Lemma splt_join_output_uniq_edge_out_rht :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A),
        io_graph_out_well_formed G2 ->
        io_uniq_edge_out
          (splt_join s ai G1 G2 ao)
          (xsplc_rht [ai] l1 l2 [ao]
             (app_rht [ai] (app_lft [ao] (io_output_evt G2))))
          (xsplc_rht [ai] l1 l2 [ao]
             (app_rht [ai] (app_rht l2 (io_input_evt (io_sngl ao))))).
    Proof.
       split.
      - apply splt_join_edge_rht.
        unfold splt_join_rht; destruct s;
          try apply bf_cpy_edge_rht;
          try apply bf_nil_edge_rht;
          apply bf_cpy_edge_add.
      - intros. apply splt_join_edge in H0.
        destruct H0 as
          [ [u [u' [H0 [H0' H0'']]]] |
            [u [u' [H0 [H0' H0'']]]] ].
        + symmetry in H0'.
          apply xsplc_lft_eq_rht in H0' as
              [[j [H1 H1']]|[j [H1 H1']]]; subst.
          * idx_neq H1' j.
          * idx_neq H1' (io_output_evt G2).
        + apply xsplc_rht_inj in H0'.
          unfold splt_join_rht in H0; destruct s;
            try (apply bf_cpy_cpy_sngls_edge in H0 as
                  [[H1 H1']|[[w [w' [H1 [H1' H1'']]]]|[H1 H1']]]);
            try (apply bf_nil_cpy_sngls_edge in H0 as
                  [[w [w' [H1 [H1' H1'']]]]|[H1 H1']]); subst;
            try reflexivity;
            try apply app_rht_inj in H0';
            try apply app_lft_inj in H0'; subst;
            try apply H in H1;
            try contradiction;
            try idx_neq H0' (io_output_evt (io_sngl ai)).
    Qed.

    (** The next few lemmas deal with the well-formedness of
        Split-Join. *)

    (** Any [splt_join_lft] is in-well-formed. *)

    Lemma splt_join_lft_in_well_formed :
      forall [l : list A]
             (s : splt)
             (ai : A) (G : io_graph l) (ao : A),
        io_graph_in_well_formed (splt_join_lft s ai G ao).
    Proof.
      intros.
      pose proof (io_sngl_well_formed ai) as [Hi _].
      pose proof (io_sngl_well_formed ao) as [Ho _].
      destruct s; unfold splt_join_lft;
        try apply bf_cpy_in_well_formed;
        try apply bf_nil_in_well_formed;
        auto.
    Qed.

    (** Any [splt_join_lft] is out-well-formed. *)

    Lemma splt_join_lft_out_well_formed :
      forall [l : list A]
             (s : splt)
             (ai : A) (G : io_graph l) (ao : A),
        io_graph_out_well_formed (splt_join_lft s ai G ao).
    Proof.
      intros.
      pose proof (io_sngl_well_formed ai) as [_ Hi].
      pose proof (io_sngl_well_formed ao) as [_ Ho].
      destruct s; unfold splt_join_lft;
        try apply bf_cpy_out_well_formed;
        try apply bf_nil_out_well_formed;
        apply bf_cpy_out_well_formed; auto.
    Qed.

    (** Any [splt_join_lft] is well-formed. *)

    Corollary splt_join_lft_well_formed :
      forall [l : list A]
             (s : splt)
             (ai : A) (G : io_graph l) (ao : A),
        io_graph_well_formed (splt_join_lft s ai G ao).
    Proof.
      split.
      - apply splt_join_lft_in_well_formed.
      - apply splt_join_lft_out_well_formed.
    Qed.

    (** Any [splt_join_rht] is well-formed. *)

    Corollary splt_join_rht_well_formed :
      forall [l : list A]
             (s : splt)
             (ai : A) (G : io_graph l) (ao : A),
        io_graph_well_formed (splt_join_rht s ai G ao).
    Proof.
      intros.
      replace s with (splt_mirr (splt_mirr s));
        try apply splt_mirr_inv.
      rewrite <- splt_join_lft_rht_mirr_eq.
      apply splt_join_lft_well_formed.
    Qed.

    (** Any [splt_join] is well-formed. *)

    Lemma splt_join_well_formed :
      forall [l1 l2 : list A]
             (s : splt)
             (ai : A) (G1 : io_graph l1) (G2 : io_graph l2) (ao : A),
        io_graph_well_formed (splt_join s ai G1 G2 ao).
    Proof.
      intros.
      pose proof (
          splt_join_lft_well_formed s ai G1 ao
        ) as [Hli Hlo].
      pose proof (
          splt_join_rht_well_formed s ai G2 ao
        ) as [Hri Hro].
      split.
      - pose proof (
            splt_join_input_evt s ai G1 G2 ao
          ) as [H0 H1].
        unfold io_graph_in_well_formed;
          intros; intro.
        apply splt_join_edge in H.
        destruct H; repeat destruct_ex_and; subst.
        + apply Hli in H.
          rewrite H0 in H2.
          apply xsplc_lft_inj in H2.
          contradiction.
        + apply Hri in H.
          rewrite H1 in H2.
          apply xsplc_rht_inj in H2.
          contradiction.
      - pose proof (
            splt_join_output_evt s ai G1 G2 ao
          ) as [H0 H1].
        unfold io_graph_out_well_formed;
          intros; intro.
        apply splt_join_edge in H.
        destruct H; repeat destruct_ex_and; subst.
        + apply Hlo in H.
          rewrite H0 in H2.
          apply xsplc_lft_inj in H2.
          contradiction.
        + apply Hro in H.
          rewrite H1 in H2.
          apply xsplc_rht_inj in H2.
          contradiction.
    Qed.

  End SpltJoin.

End IOGraphOps.

Unset Implicit Arguments.
