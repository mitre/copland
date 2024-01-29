(** A representation of all subsets of a universal set containing all
    members of a type *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import List ListSet.
Import ListNotations.

Require Import Preamble.

Set Implicit Arguments.

Section AllSet.

  Variable A : Type.
  Hypothesis Aeq_dec : forall (x y : A), {x = y} + {x <> y}.

  Inductive aset : Type :=
  | All
  | ASet (s : set A).

  (** Inject a singleton into [aset]. *)

  Definition aset_sngl (a : A) : aset := ASet [a].

  (** Set membership *)

  Definition aset_mem (a : A) (S : aset) : bool :=
    match S with
    | All => true
    | ASet s =>
        set_mem Aeq_dec a s
    end.

  (** An [aset] with a member is not empty. *)

  Lemma aset_mem_nonempty :
    forall (S : aset) a,
      aset_mem a S = true -> S <> ASet [].
  Proof.
    destruct S; intros; intro;
      try discriminate.
    injection H0 as H0; subst.
    discriminate.
  Qed.

  (** A singleton [aset] has only one member. *)

  Lemma aset_mem_sngl :
    forall (a a' : A),
      aset_mem a (aset_sngl a') = true -> a = a'.
  Proof.
    simpl; intros.
    destruct (Aeq_dec a a'); try discriminate; auto.
  Qed.

  (** If an [ASet] already contains an element, adding an additional
      element with cons does not change that. *)

  Lemma aset_mem_cons :
    forall (s : set A) a a',
      aset_mem a (ASet s) = true -> aset_mem a (ASet (a' :: s)) = true.
  Proof.
    simpl; intros.
    destruct (Aeq_dec a a');
      try rewrite H; auto.
  Qed.

  (** Is an [aset] a subset of a singleton? *)

  Definition aset_subset_snglb (S : aset) (a : A) : bool :=
    match S with
    | All => false
    | ASet [] => true
    | ASet [a'] =>
        if Aeq_dec a' a then true else false
    | _ => false
    end.

  (** A singleton is always a subset of itself. *)

  Lemma aset_subset_snglb_refl :
    forall (a : A), aset_subset_snglb (aset_sngl a) a = true.
  Proof.
    simpl; intros.
    destruct (Aeq_dec a a); auto; contradiction.
  Qed.

  (** If an [aset] is a subset of a singleton, it is either empty or
      just that singleton. *)

  Lemma aset_subset_snglb_cases :
    forall (S : aset) (a : A),
      aset_subset_snglb S a = true <-> S = ASet [] \/ S = ASet [a].
  Proof.
    split.
    - destruct S; simpl; intros; try discriminate.
      destruct s as [|a' s];
        try destruct s;
        try destruct (Aeq_dec a' a); subst;
        try discriminate; auto.
    - intros [H|H]; subst; simpl; auto.
      destruct (Aeq_dec a a); auto; contradiction.
  Qed.

  (** Intersection *)

  Definition aset_inter (S S' : aset) : aset :=
    match S, S' with
    | All, _ => S'
    | _, All => S
    | ASet s, ASet s' =>
        ASet (set_inter Aeq_dec s s')
    end.

  (** A member of the intersection of [aset]s is a member of both. *)

  Lemma aset_inter_mem :
    forall (S S' : aset) (a : A),
      aset_mem a (aset_inter S S') = true <->
      aset_mem a S = true /\ aset_mem a S' = true.
  Proof.
    split.
    - destruct S, S'; simpl; intros; auto.
      apply set_mem_correct1 in H.
      apply set_inter_elim in H as [H0 H1].
      apply (set_mem_correct2 Aeq_dec) in H0, H1.
      intuition.
    - intros [H0 H1].
      destruct S, S'; simpl; auto.
      apply set_mem_correct1 in H0, H1.
      pose proof (set_inter_intro Aeq_dec _ _ _ H0 H1).
      apply (set_mem_correct2 Aeq_dec) in H.
      assumption.
  Qed.

  (** An intersection with a singleton [aset] on the left is nonempty
      iff the singleton's element is in the other [aset]. *)

  Lemma aset_inter_sngl_nonempty_lft :
    forall (a : A) (S : aset),
      aset_inter (aset_sngl a) S <> ASet [] <-> aset_mem a S = true.
  Proof.
    split; intros.
    - destruct S; simpl in *; auto.
      destruct (set_mem Aeq_dec a s);
        try contradiction; auto.
    - intro. destruct S; simpl in *;
        try discriminate.
      destruct (set_mem Aeq_dec a s);
        try discriminate; auto.
  Qed.

  (** If an intersection with a singleton [aset] on the left yields a
      singleton, the two singletons are identical. *)

  Lemma aset_inter_sngls_lft :
    forall (a a' : A) (S : aset),
      aset_inter (aset_sngl a) S = aset_sngl a' -> a = a'.
  Proof.
    destruct S; simpl; intros;
      try destruct (set_mem Aeq_dec a s);
      try injection H as H; auto;
      try discriminate.
  Qed.

  (** An intersection with a singleton on the left is always a subset
      of that singleton. *)

  Lemma aset_inter_sngl_subset_lft :
    forall (a : A) (S : aset),
      aset_subset_snglb (aset_inter (aset_sngl a) S) a = true.
  Proof.
    destruct S; simpl; [
      | destruct (set_mem Aeq_dec a s); auto
      ]; destruct (Aeq_dec a a); try contradiction; auto.
  Qed.

  (** An intersection is [All] only when both sets are [All]. *)

  Lemma aset_inter_all :
    forall (S S' : aset),
      aset_inter S S' = All -> S = All /\ S' = All.
  Proof.
    destruct S; destruct S'; simpl;
      intros; try discriminate; auto.
  Qed.

  (** Union *)

  Definition aset_union (S S' : aset) : aset :=
    match S, S' with
    | ASet s, ASet s' =>
        ASet (set_union Aeq_dec s s')
    | _, _ => All
    end.

  (** An [aset] union has a member iff one of the constituents does. *)

  Lemma aset_union_mem :
    forall (S S' : aset) a,
      aset_mem a (aset_union S S') = true <->
        aset_mem a S = true \/ aset_mem a S' = true.
  Proof.
    split; intros.
    - destruct S, S'; simpl in *; auto.
      apply set_mem_correct1 in H.
      apply set_union_elim in H.
      destruct H; [left | right];
        apply set_mem_correct2; auto.
    - destruct S, S'; simpl in *; auto.
      destruct H;
        apply set_mem_correct1 in H; [
          eapply set_union_intro1 in H |
          eapply set_union_intro2 in H
        ]; apply set_mem_correct2; eauto.
  Qed.

End AllSet.

Unset Implicit Arguments.
