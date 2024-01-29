(** Various utilities *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import Lia List ListSet PeanoNat.
Import ListNotations.

Ltac inv H := inversion H; subst; clear H.

Ltac rev_induction X := pattern X; apply rev_ind; intros; subst; auto.

(** Unpack an equality between lists in which one list is known to
    have an element. *)

Ltac list_eq H pi :=
  destruct pi; simpl in H; try discriminate; injection H as H; subst.

(** Expand let expressions in both antecedent and conclusion. *)

Ltac expand_let_pairs :=
  match goal with
  | |- context [let (_,_) := ?e in _] =>
    rewrite (surjective_pairing e)
  | [ H: context [let (_,_) := ?e in _] |- _ ] =>
    rewrite (surjective_pairing e) in H
  end.

(** Destruct conjunctions and existential quantifications in the
    antecedent. *)

Ltac destruct_ex_and :=
  match goal with
  | [ H: _ /\ _ |- _ ] =>
    destruct H
  | [ H: exists _, _ |- _ ] =>
    destruct H
  end.

(** Injectivity of general functions *)

Definition inj {A B} (f : A -> B) : Prop :=
  forall a a', f a = f a' -> a = a'.

(** Boolean-valued decidable equality of lists *)

Definition list_eqb {A : Type}
  (Aeq_dec : forall x y : A, {x = y} + {x <> y})
  (l l' : list A) : bool :=
  if list_eq_dec Aeq_dec l l' then true else false.

(** [list_eqb] is reflexive *)

Lemma list_eqb_refl :
  forall [A] Aeq_dec (l : list A), list_eqb Aeq_dec l l = true.
Proof.
  unfold list_eqb; intros.
  destruct (list_eq_dec Aeq_dec l l); auto.
Qed.

(** Useful in contexts where [simpl] goes too far. *)

Lemma map_nil : forall {A B} (f : A -> B), map f [] = [].
Proof. auto. Qed.

(** A nonempty list is nonempty. *)

Lemma cons_neq_nil :
  forall [A] (pi : list A) a, a :: pi <> [].
Proof.
  intros; intro; discriminate.
Qed.

(** Analogue of [cons_neq_nil] for appends *)

Lemma app_neq_nil :
  forall [A] (pi : list A) a, pi ++ [a] <> [].
Proof.
  intros. intro.
  destruct pi; simpl in *; discriminate.
Qed.

(** A basic fact about nonempty lists *)

Lemma nonempty_list_shape : forall [A] (l : list A),
    0 < length l -> exists a l', l = a :: l'.
Proof.
  destruct l; simpl; intros; try lia.
  exists a, l. auto.
Qed.

(** A list is empty iff its reverse is. *)

Lemma nil_iff_rev_nil : forall [A] (l : list A),
    l = [] <-> rev l = [].
Proof.
  destruct l; simpl; try reflexivity.
  split; intros; try discriminate.
  destruct (rev l); simpl in *; discriminate.
Qed.

(** Basic facts about [nat] differences

    These lemmas are used to define functions of list indices in proof
    mode.  For predictability reasons, we choose to give fully manual
    proofs of them instead of using something like [lia] to dispatch
    them automatically. *)

Lemma nat_sub_lt : forall n m p,
    n < m + p -> m <= n -> n - m < p.
Proof.
  intros n m. revert n.
  induction m; simpl; intros.
  - rewrite Nat.sub_0_r. assumption.
  - destruct n; simpl in *.
    + inversion H0.
    + apply Nat.succ_lt_mono in H.
      apply Nat.succ_le_mono in H0.
      apply IHm; assumption.
Qed.

Lemma nat_sub_rev : forall n m,
    n < m -> m - n - 1 < m.
Proof.
  intros n m. revert n.
  induction m; simpl; intros.
  - apply Nat.nlt_0_r in H.
    contradiction.
  - destruct n; simpl in *.
    + rewrite Nat.sub_0_r.
      apply Nat.lt_succ_diag_r.
    + apply Nat.succ_lt_mono in H.
      apply IHm in H.
      apply Nat.lt_trans with (m := m).
      * assumption.
      * apply Nat.lt_succ_diag_r.
Qed.

(** Map a function over a pair of elements of the same type. *)

Definition map_pair {A B} (f : A -> B) (p : A * A) : B * B :=
  (f (fst p), f (snd p)).

(** Relates the inputs and outputs of [map_pair] via the passed
    function. *)

Lemma expand_map_pair : forall A B (f : A -> B) (a a' : A) (b b' : B),
    map_pair f (a, a') = (b, b') ->
    b = f a /\ b' = f a'.
Proof.
  unfold map_pair. simpl. intros.
  injection H as H0 H1. intuition.
Qed.
