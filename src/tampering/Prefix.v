(** List prefixes *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import Lia List PeanoNat.
Import ListNotations.

Require Import Index Preamble.

(** Take prefix [0; ...; S (idx_nat i)] from a (nonempty) list. *)

Definition take_prfx [A] [l : list A] (i : idx l) := firstn (S (idx_nat i)) l.

(** Asserts that [l'] is a prefix of [l]. *)

Definition prfx [A] (l' l : list A) := exists (i : idx l), l' = take_prfx i.

(** A [take_prfx] is always [prfx] for the original list. *)

Lemma take_prfx_is_prfx : forall [A] [l : list A] (i : idx l),
    prfx (take_prfx i) l.
Proof.
  intros; exists i; auto.
Qed.

(** A singleton list has a unique prefix. *)

Lemma prfx_sngl : forall [A] (a : A) l,
    prfx l [a] -> l = [a].
Proof.
  intros A a l [i H].
  unfold take_prfx in H.
  rewrite (idx_sngl i) in H.
  simpl in H; auto.
Qed.

(** Taking a prefix of maximal length yields the entire list. *)

Lemma take_prfx_all : forall [A] [l : list A] (i : idx l),
    idx_nat i = length l - 1 ->
    take_prfx i = l.
Proof.
  unfold take_prfx. intros.
  rewrite H.
  assert (0 < length l) by (destruct i; lia).
  assert (S (length l - 1) = length l) by lia.
  rewrite H1. apply firstn_all.
Qed.

(** A prefix of a list appended with a singleton is either a prefix of
    the original list or is equal to the append itself. *)

Lemma prfx_app : forall [A] (l l' : list A) (a : A),
    prfx l' (l ++ [a]) ->
    prfx l' l \/ l' = l ++ [a].
Proof.
  induction l; intros.
  - simpl in *. right.
    apply prfx_sngl; auto.
  - destruct H as [i H].
    unfold take_prfx in H.
    destruct i as [n Hn].
    simpl in H, Hn.
    assert (
        S n < S (length (l ++ [a0]))
        \/ S n = S (length (l ++ [a0]))
      ) by lia.
    destruct H0.
    + (* Prefix of l *)
      assert (n < length (l ++ [a0])) by lia.
      rewrite app_length in H1. simpl in H1.
      assert (n <= length l) by lia.
      assert (n - length l = 0) by lia.
      rewrite firstn_app in H.
      rewrite H3 in H. simpl in H.
      rewrite app_nil_r in H.
      assert (n < length (a :: l)) by (simpl; lia).
      left. exists (to_idx H4).
      unfold take_prfx. simpl; auto.
    + (* Equal to l ++ [a0] *)
      assert (n = length (l ++ [a0])) by lia.
      subst n. rewrite firstn_all in H.
      right; auto.
Qed.

(** The same list results from taking a prefix from an append versus
    from only the left list in the append when the index belongs to
    the left list. *)

Lemma prfx_lft :
  forall [A] (l l' : list A) (i : idx (l ++ l')) (Hi : idx_nat i < length l),
    take_prfx i = take_prfx (to_idx Hi).
Proof.
  intros A l l' i.
  rewrite (to_idx_nat_evi i).
  destruct i as [n Hn].
  simpl; intros.
  unfold take_prfx. simpl idx_nat.
  assert (S n - length l = 0) by lia.
  rewrite firstn_app. rewrite H.
  rewrite firstn_O. rewrite app_nil_r.
  reflexivity.
Qed.

(** Convenience lemma for taking a prefix of length 2 when the first
    and second elements of the list are known. *)

Lemma take_two :
  forall [A] (l : list A) a a' (H0 : 0 < length l) (H1 : 1 < length l),
    nth_safe l (to_idx H0) = a ->
    nth_safe l (to_idx H1) = a' ->
    take_prfx (to_idx H1) = [a; a'].
Proof.
  intros.
  pose proof (
      nonempty_list_shape l H0
    ) as [x [l' H3]].
  subst l. simpl in H. subst x.
  assert (0 < length l') by (simpl in *; lia).
  pose proof (
      nonempty_list_shape l' H
    ) as [y [l'' H4]].
  subst l'. simpl in H2. subst y.
  reflexivity.
Qed.
