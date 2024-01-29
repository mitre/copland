(** Indices providing safe access to list elements *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Lia List PeanoNat.
Import ListNotations.

Require Import Preamble.

Set Implicit Arguments.

(** * Basic definitions *)

Section IndexDefn.

  Variable A : Type.
  Variable l : list A.

  (** The type of valid indices into [l]

      Can be thought of at a [nat n] together with evidence [Hn] that
      [n < length l]. *)

  Definition idx := { n : nat | n < length l }.

  (** Project an [idx] to its underlying [nat] and evidence. *)

  Definition idx_nat (i : idx) := proj1_sig i.
  Definition idx_evi (i : idx) := proj2_sig i.

  Lemma idx_nat_lt_length : forall i, idx_nat i < length l.
  Proof.
    destruct i as [n Hn]. apply Hn.
  Qed.

  (** The evidence bundled into an [idx] is only there to guarantee
      the safety of list accesses.  We do not introspect it otherwise.
      Conceptually, this gives us the freedom to view the indices for
      a given list as simple natural numbers, exactly as in the unsafe
      setting.  In line with this view, we use the axiom of proof
      irrelevance in the following lemma to prove that two [idx l] are
      equal iff their underlying [nat] values are equal. *)

  Lemma idx_eq_iff : forall i j, i = j <-> idx_nat i = idx_nat j.
  Proof.
    destruct i as [n Hn].
    destruct j as [m Hm].
    simpl. split; intro.
    - injection H as H. assumption.
    - subst. rewrite (
          proof_irrelevance (m < length l) Hn Hm
        ). reflexivity.
  Qed.

  (** Decidable equality of [idx] from that of [nat]

      This is needed so that [idx] may be used with ListSet, which
      requires decidable equality of set elements. *)

  Definition idx_eq_dec : forall (i j : idx), {i = j} + {i <> j}.
  Proof.
    intros. destruct (
        Nat.eq_dec (idx_nat i) (idx_nat j)
      ) as [Hl|Hr].
    - left. apply idx_eq_iff. assumption.
    - right. intro. apply idx_eq_iff in H.
      apply Hr in H. contradiction.
  Defined.

  (** Convert a [nat] and evidence into an [idx]. *)

  Definition to_idx n Hn := exist (fun n => n < length l) n Hn.

  Lemma to_idx_nat_evi : forall i, i = @to_idx (idx_nat i) (idx_evi i).
  Proof.
    destruct i. reflexivity.
  Qed.

  Lemma to_idx_eq : forall n (Hn Hn' : n < length l),
      to_idx Hn = to_idx Hn'.
  Proof.
    intros. apply idx_eq_iff. reflexivity.
  Qed.

End IndexDefn.

(* By default, Coq requires us to state [l] explicitly in calls to
   [to_idx], but we can always infer it from the type of [Hn]. *)
Global Arguments to_idx [A] [l] [n].

(** * Basic results about indices *)

Section IndexBasics.

  Variable A : Type.

  (** A singleton list has a single index. *)

  Lemma idx_sngl : forall (a : A) (i : idx [a]),
      idx_nat i = 0.
  Proof.
    destruct i as [n Hn].
    simpl in *. lia.
  Qed.

  (** A useful result relating the upper indices of [l1 ++ l2] to the
      indices of [l2]. *)

  Lemma app_idx_rht_bnd : forall (l1 l2 : list A) (i : idx (l1 ++ l2)),
      length l1 <= idx_nat i ->
      idx_nat i - length l1 < length l2.
  Proof.
    destruct i as [n Hn]. simpl.
    rewrite app_length in Hn.
    apply nat_sub_lt; auto.
  Qed.

  Lemma app3_idx_nat_range :
    forall (l1 l2 l3 : list A) (i : idx (l1 ++ l2 ++ l3)),
      idx_nat i < length l1
      \/ length l1 <= idx_nat i < length l1 + length l2
      \/ length l1 + length l2 <= idx_nat i < length l1 + length l2 + length l3.
  Proof.
    intros. destruct i as [n Hn]. simpl.
    repeat rewrite app_length in Hn. lia.
  Qed.

  Lemma app4_idx_nat_range :
    forall (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l3++l4)),
      idx_nat i < length l1
      \/ length l1 <= idx_nat i < length l1 + length l2
      \/ length l1 + length l2 <= idx_nat i < length l1 + length l2 + length l3
      \/ length l1 + length l2 + length l3 <= idx_nat i < length l1 + length l2 + length l3 + length l4.
  Proof.
    intros. destruct i as [n Hn]. simpl.
    repeat rewrite app_length in Hn. lia.
  Qed.

End IndexBasics.

(** * Safe list access *)

Section NthSafe.

  (** ** The [nth_safe] function, basic results *)

  Section NthSafeDefn.

    Local Unset Implicit Arguments.

    (** Return the element of [l] at the index represented by [i] *)

    Fixpoint nth_safe {A} (l : list A) (i : idx l) : A.
    Proof.
      destruct i as [n Hn].
      destruct l as [|a l'].
      - simpl in Hn.
        apply Nat.nlt_0_r in Hn.
        contradiction.
      - destruct n.
        + apply a.
        + simpl in Hn.
          apply Nat.succ_lt_mono in Hn.
          apply (nth_safe A l' (@to_idx _ _ n Hn)).
    Defined.

  End NthSafeDefn.

  (** [nth_safe] is independent of evidence. *)

  Lemma nth_safe_evi_indep : forall [A] (l : list A) n (Hn Hn' : n < length l),
      nth_safe l (to_idx Hn) = nth_safe l (to_idx Hn').
  Proof.
    (* There is a trivial proof to be had here based on proof
    irrelevance.  We opt for this longer one because it exercises the
    definition of [nth_safe] explicitly *)
    induction l; intros.
    - simpl in Hn. lia.
    - destruct n.
      + reflexivity.
      + apply IHl.
  Qed.

  (** Indices into the same list with the same underlying [nat] value
      are identical for [nth_safe]. *)

  Corollary nth_safe_nat_eq : forall [A] (l : list A) (i j : idx l),
      idx_nat i = idx_nat j ->
      nth_safe l i = nth_safe l j.
  Proof.
    intros.
    rewrite (to_idx_nat_evi i) in *.
    rewrite (to_idx_nat_evi j) in *.
    destruct i as [n Hn]; destruct j as [m Hm].
    simpl in *; subst.
    apply nth_safe_evi_indep.
  Qed.

  (** Fully specifies the behavior of [nth_safe] for singleton lists. *)

  Lemma nth_safe_sngl : forall [A] (a : A) (i : idx [a]),
      nth_safe [a] i = a.
  Proof.
    intros.
    pose proof (idx_sngl i).
    destruct i as [n Hn].
    simpl in H. subst.
    reflexivity.
  Qed.

  (** The first element of a list has index 0. *)

  Lemma nth_safe_fst : forall [A] (l : list A) a i,
      idx_nat i = 0 -> nth_safe (a :: l) i = a.
  Proof.
    intros. rewrite (to_idx_nat_evi i).
    destruct i as [n Hn];
      simpl in *; subst; auto.
  Qed.

  (** [nth_safe], [cons] and [S] have the right relationship. *)

  Lemma nth_safe_cons : forall [A] (l : list A) a n HSn Hn,
      nth_safe (a :: l) (@to_idx _ _ (S n) HSn) = nth_safe l (@to_idx _ _ n Hn).
  Proof.
    induction l; intros.
    - simpl in Hn. lia.
    - destruct n.
      + reflexivity.
      + destruct l.
        * simpl in Hn. lia.
        * apply IHl.
  Qed.

  (** For indices less than the length of the first list in an append,
      [nth_safe] returns a value from the first list. *)

  Lemma nth_safe_app_lft :
    forall [A] (l1 l2 : list A) i (Hn' : idx_nat i < length l1),
      nth_safe (l1 ++ l2) i = nth_safe l1 (to_idx Hn').
  Proof.
    intros A l1 l2 i.
    rewrite (to_idx_nat_evi i).
    destruct i as [n Hn]. simpl.
    generalize dependent n. revert l2.
    induction l1; intros.
    - simpl in Hn'. lia.
    - destruct n.
      + reflexivity.
      + apply IHl1.
  Qed.

  (** For indices at least the length of the first list in an append,
      [nth_safe] returns a value from the second list.

      Note that [idx_app_rht_bnd] furnishes a proof of the type of
      [Hn'] whenever the precondition [length l1 <= idx_nat i] holds. *)

  Lemma nth_safe_app_rht : forall [A] (l1 l2 : list A) i,
      length l1 <= idx_nat i ->
      forall (Hn' : idx_nat i - length l1 < length l2),
        nth_safe (l1 ++ l2) i = nth_safe l2 (to_idx Hn').
  Proof.
    intros A l1 l2 i.
    rewrite (to_idx_nat_evi i).
    destruct i as [n Hn]. simpl.
    generalize dependent n. revert l2.
    induction l1; intros.
    - simpl in *. revert Hn'.
      rewrite Nat.sub_0_r.
      intro. apply nth_safe_evi_indep.
    - destruct n; simpl in *;
        try apply IHl1; try lia.
  Qed.

  (** Combines two preceding lemmas to fully characterize the results
      of [nth_safe (l1 ++ l2) i] relative to the elements of [l1] and
      [l2]. *)

  Corollary nth_safe_app : forall [A] (l1 l2 : list A) (i : idx (l1 ++ l2)),
      (idx_nat i < length l1 /\
         forall (Hn' : idx_nat i < length l1),
           nth_safe (l1 ++ l2) i = nth_safe l1 (to_idx Hn'))
      \/ (length l1 <= idx_nat i /\
            forall (Hn' : idx_nat i - length l1 < length l2),
              nth_safe (l1 ++ l2) i = nth_safe l2 (to_idx Hn')).
  Proof.
    intros. destruct (
        le_le_S_dec (length l1) (idx_nat i)
      ) as [Hl | Hr]; [right | left];
      split; auto; intros.
    - apply nth_safe_app_rht; auto.
    - apply nth_safe_app_lft.
  Qed.

  (** [nth_safe] and [map] have the right relationship. *)

  Lemma nth_safe_map :
    forall [A B] (l : list A) (f : A -> B) (i : idx l) (i' : idx (map f l)),
      idx_nat i' = idx_nat i -> nth_safe (map f l) i' = f (nth_safe l i).
  Proof.
    induction l.
    - destruct i; simpl in *; lia.
    - intros f i.
      destruct l; rewrite map_cons;
        [rewrite map_nil | ]; intros.
      + repeat rewrite nth_safe_sngl; auto.
      + rewrite (to_idx_nat_evi i).
        rewrite (to_idx_nat_evi i').
        destruct i as [n Hn].
        destruct i' as [n' Hn'].
        unfold idx_evi, proj2_sig.
        simpl in H. destruct n; subst n'; auto.
        (* simpl goes too far, hence these tedious asserts *)
        assert (
            length (a :: a0 :: l) = S (length (a0 :: l))
          ) by reflexivity.
        assert (
            length (f a :: map f (a0 :: l)) = S (length (map f (a0 :: l)))
          ) by reflexivity.
        assert (n < length (a0 :: l)) by lia.
        assert (n < length (map f (a0 :: l))) by lia.
        assert (idx_nat (to_idx H2) = idx_nat (to_idx H1)) by auto.
        apply IHl in H3.
        rewrite <- (nth_safe_cons Hn' H2) in H3.
        rewrite <- (nth_safe_cons Hn H1) in H3.
        assumption.
  Qed.

  (** ** Results about [nth_safe] and list reversal *)

  Section NthSafeRev.

    Variable A : Type.

    (** Relates indices and elements of a list and its reverse. *)

    Lemma nth_safe_rev_full : forall (l : list A) i Hn',
        nth_safe (rev l) (@to_idx _ _ (length l - idx_nat i - 1) Hn') = nth_safe l i.
    Proof.
      intros l i. rewrite (to_idx_nat_evi i).
      destruct i as [n Hn]. simpl.
      generalize dependent n.
      induction l; intros.
      - simpl in Hn. lia.
      - destruct n; simpl in *.
        + revert Hn'. rewrite Nat.sub_0_r.
          intro. assert (
              H' : length (rev l) <= idx_nat (to_idx Hn')
            ). { rewrite rev_length. auto. }
          pose proof (nth_safe_app_rht _ _ _ H').
          revert H. rewrite rev_length. simpl.
          rewrite Nat.sub_diag. intuition.
        + assert (
              H' : idx_nat (to_idx Hn') < length (rev l)
            ). { simpl. rewrite rev_length. lia. }
          rewrite (nth_safe_app_lft _ _ _ H').
          apply IHl.
    Qed.

    (** Map an [idx l] to its analogue in [idx (rev l)]. *)

    Definition rev_idx (l : list A) (i : idx l) : idx (rev l).
    Proof.
      destruct i as [n Hn].
      apply nat_sub_rev in Hn.
      assert (Hn' : length l - n - 1 < length (rev l)).
      { rewrite rev_length. assumption. }
      apply (@to_idx _ _ (length l - n - 1) Hn').
    Defined.

    (** A clean consequence of [nth_safe_rev_full]. *)

    Lemma nth_safe_rev : forall (l : list A) i,
        nth_safe (rev l) (rev_idx i) = nth_safe l i.
    Proof.
      intros.
      pose proof (nth_safe_rev_full i).
      destruct i as [n Hn]. simpl. apply H.
    Qed.

    (** Two indices are equal iff their [rev_idx] counterparts are. *)

    Lemma rev_idx_eq_iff :
      forall (l : list A) (i j : idx l), i = j <-> rev_idx i = rev_idx j.
    Proof.
      intros. repeat rewrite idx_eq_iff.
      destruct i as [n Hn]; destruct j as [m Hm].
      simpl; lia.
    Qed.

    (** Every [idx (rev l)] has a [rev_idx] preimage in [idx l]. *)

    Lemma rev_idx_preimage :
      forall (l : list A) (i : idx (rev l)), exists i', i = rev_idx i'.
    Proof.
      intros.
      rewrite (to_idx_nat_evi i).
      destruct i as [n Hn]; simpl.
      assert (length l - n - 1 < length l).
      { rewrite rev_length in Hn; lia. }
      exists (to_idx H).
      rewrite idx_eq_iff; simpl.
      rewrite rev_length in Hn. lia.
    Qed.

  End NthSafeRev.

  Section FstLstElem.

    Variable A : Type.

    (** Asserts that [a] is the first element of [l]. *)

    Definition fst_elem (l : list A) a :=
      exists (i : idx l), idx_nat i = 0 /\ nth_safe l i = a.

    (** Asserts that [a] is the last element of [l]. *)

    Definition lst_elem (l : list A) a :=
      exists (i : idx l), idx_nat i = length l - 1 /\ nth_safe l i = a.

    (** A list whose first and last elements differ has length greater
        than 1. *)

    Lemma length_fst_lst_neq : forall (l : list A) a a',
        fst_elem l a -> lst_elem l a' -> a <> a' -> 1 < length l.
    Proof.
      intro.
      assert (length l <= 1 \/ 1 < length l) by lia.
      intros; destruct H; auto.
      destruct H0 as [i [H0 H0']].
      destruct H1 as [j [H1 H1']].
      rewrite (to_idx_nat_evi i) in *.
      rewrite (to_idx_nat_evi j) in *.
      destruct i as [n Hn]; destruct j as [m Hm].
      assert (length l = 0 \/ length l = 1) by lia.
      destruct H3; simpl in *; try lia.
      rewrite H3 in *; simpl in *; subst.
      pose proof (nth_safe_evi_indep l Hn Hm).
      contradiction.
    Qed.

    (** An element prepended to the front of a list becomes its
        [fst_elem]. *)

    Lemma fst_elem_cons : forall (l : list A) a,
        fst_elem (a :: l) a.
    Proof.
      intros.
      assert (0 < length (a :: l)) by (simpl; lia).
      exists (to_idx H). auto.
    Qed.

    (** An alternate version of the previous lemma *)

    Lemma fst_elem_cons' : forall (l : list A) a a',
        fst_elem (a :: l) a' -> a = a'.
    Proof.
      intros.
      destruct H as [i [H0 H1]].
      rewrite (to_idx_nat_evi i) in *.
      destruct i as [n Hn]; simpl idx_evi in *.
      simpl in H0. subst n. simpl in H1. auto.
    Qed.

    (** The [lst_elem] of a singleton is the single event. *)

    Lemma lst_elem_sngl : forall (a a' : A),
        lst_elem [a] a' -> a = a'.
    Proof.
      unfold lst_elem; intros.
      destruct H as [i [H H']].
      rewrite nth_safe_sngl in H'; auto.
    Qed.

    (** Prepending an element does not affect [lst_elem]. *)

    Lemma lst_elem_cons : forall (l : list A) a a',
        lst_elem l a -> lst_elem (a' :: l) a.
    Proof.
      unfold lst_elem; intros.
      destruct H as [i [H H']].
      rewrite (to_idx_nat_evi i) in *.
      destruct i as [n Hn].
      simpl in H, H'; subst n.
      assert (
          length (a' :: l) - 1 < length (a' :: l)
        ) by (simpl; lia).
      exists (to_idx H). split; auto.
      assert (
          S (length l - 1) < length (a' :: l)
        ) by (simpl; lia).
      rewrite <- (nth_safe_cons H0) in H'.
      rewrite <- H'.
      apply nth_safe_nat_eq. simpl; lia.
    Qed.

    (** Provides a converse to [lst_elem_cons] under the additional
        assumption that [l <> []]. *)

    Lemma lst_elem_cons_conv : forall (l : list A) a a',
        l <> [] ->
        lst_elem (a' :: l) a -> lst_elem l a.
    Proof.
      unfold lst_elem; intros.
      destruct H0 as [i [H0 H0']].
      rewrite (to_idx_nat_evi i) in *.
      destruct i as [n Hn]. simpl in H0.
      rewrite Nat.sub_0_r in H0; subst n.
      simpl idx_evi in H0'.
      assert (length l - 1 < length l). {
        destruct l; simpl; try contradiction; lia.
      }
      exists (to_idx H0). split; auto.
      assert (
          S (length l - 1) < length (a' :: l)
        ) by (simpl; lia).
      rewrite <- (nth_safe_cons H1).
      rewrite <- H0'.
      apply nth_safe_nat_eq. simpl; lia.
    Qed.

    (** Reversing a list sends its [fst_elem] to its [lst_elem] (and
        vice versa). *)

    Lemma fst_lst_rev : forall (l : list A) a,
        fst_elem l a <-> lst_elem (rev l) a.
    Proof.
      unfold fst_elem, lst_elem.
      split; intros [i [H H']].
      - exists (rev_idx i). split.
        + rewrite rev_length.
          destruct i as [n Hn].
          simpl in *; subst. lia.
        + rewrite nth_safe_rev; auto.
      - assert (0 < length l). {
          destruct i as [n Hn].
          clear H'; simpl in *.
          rewrite rev_length in *.
          rewrite H in Hn; lia.
        }
        assert (rev_idx (to_idx H0) = i). {
          rewrite idx_eq_iff.
          rewrite H, rev_length.
          simpl; lia.
        }
        exists (to_idx H0). split; auto.
        rewrite <- nth_safe_rev.
        rewrite H1. assumption.
    Qed.

  End FstLstElem.

End NthSafe.

(** * Injecting [idx] through list appends *)

Section AppInj.

  Variable A : Type.

  Section AppLftRht.

    (** Map an [idx l1] to an [idx (l1 ++ l2)].  The underlying [nat]
        value is unchanged. *)

    Definition app_lft (l1 l2 : list A) (i : idx l1) : idx (l1 ++ l2).
    Proof.
      destruct i as [n Hn].
      apply (Nat.lt_lt_add_r _ _ (length l2)) in Hn.
      rewrite <- app_length in Hn.
      apply (@to_idx _ _ n Hn).
    Defined.

    (** Map an [idx l2] to an [idx (l1 ++ l2)].  The underlying [nat]
        value is increased by [length l1]. *)

    Definition app_rht (l1 l2 : list A) (i : idx l2) : idx (l1 ++ l2).
    Proof.
      destruct i as [n Hn].
      rewrite (Nat.add_lt_mono_r _ _ (length l1)) in Hn.
      rewrite (Nat.add_comm (length l2)) in Hn.
      rewrite <- app_length in Hn.
      apply (@to_idx _ _ (n + length l1) Hn).
    Defined.

    (** The next two results characterize the effects of [app_lft] and
        [app_rht] on [idx_nat i]. *)

    Lemma idx_nat_app_lft : forall (l1 l2 : list A) (i : idx l1),
        idx_nat (app_lft l2 i) = idx_nat i.
    Proof.
      intros. destruct i as [n Hn]. reflexivity.
    Qed.

    Lemma idx_nat_app_rht : forall (l1 l2 : list A) (i : idx l2),
        idx_nat (app_rht l1 i) = idx_nat i + length l1.
    Proof.
      intros. destruct i as [n Hn]. reflexivity.
    Qed.

    (** The next two results show that [app_lft] and [app_rht] are
        injective. *)

    Lemma app_lft_inj : forall (l1 l2 : list A), inj (@app_lft l1 l2).
    Proof.
      unfold inj. intros.
      rewrite idx_eq_iff in H.
      repeat rewrite idx_nat_app_lft in H.
      apply idx_eq_iff. assumption.
    Qed.

    Lemma app_rht_inj : forall (l1 l2 : list A), inj (@app_rht l1 l2).
    Proof.
      unfold inj. intros.
      rewrite idx_eq_iff in H.
      repeat rewrite idx_nat_app_rht in H.
      rewrite Nat.add_cancel_r in H.
      apply idx_eq_iff. assumption.
    Qed.

    (** The next two results show that every index of [l1 ++ l2] can
        be written as an [app_lft l2] or [app_rht l1] of some [idx l1]
        or [idx l2], respectively. *)

    Lemma app_idx_lft :
      forall (l1 l2 : list A) (i : idx (l1 ++ l2)) (Hl : idx_nat i < length l1),
        i = app_lft l2 (to_idx Hl).
    Proof.
      intros l1 l2 i.
      rewrite (to_idx_nat_evi i).
      destruct i as [n Hn].
      simpl. intro.
      apply to_idx_eq.
    Qed.

    Lemma app_idx_rht : forall (l1 l2 : list A) (i : idx (l1 ++ l2)),
        length l1 <= idx_nat i ->
        forall (Hr : idx_nat i - length l1 < length l2),
          i = app_rht l1 (to_idx Hr).
    Proof.
      intros l1 l2 i.
      rewrite (to_idx_nat_evi i).
      destruct i as [n Hn].
      simpl. intros.
      (* Replace the RHS with a less-constrained equivalent *)
      assert (
          Hn' : n - length l1 + length l1 < length (l1 ++ l2)
        ) by lia.
      rewrite <- (to_idx_eq _ Hn').
      revert Hn'. rewrite Nat.sub_add; auto.
      apply to_idx_eq.
    Qed.

    (** [app_lft] preserves the result of [nth_safe]. *)

    Lemma app_lft_nth_safe : forall (l1 l2 : list A) (i : idx l1),
        nth_safe (l1 ++ l2) (app_lft l2 i) = nth_safe l1 i.
    Proof.
      intros.
      rewrite (to_idx_nat_evi i).
      apply nth_safe_app_lft.
    Qed.

    (** [app_rht] preserves the result of [nth_safe]. *)

    Lemma app_rht_nth_safe : forall (l1 l2 : list A) (i : idx l2),
        nth_safe (l1 ++ l2) (app_rht l1 i) = nth_safe l2 i.
    Proof.
      intros.
      assert (H : length l1 <= idx_nat (app_rht l1 i)).
      { destruct i. simpl. lia. }
      pose proof (app_idx_rht_bnd _ _ _ H).
      pose proof (nth_safe_app_rht _ _ _ H).
      rewrite (H1 H0). revert H0.
      rewrite (to_idx_nat_evi i).
      destruct i as [n Hn]. simpl.
      rewrite Nat.add_sub. intro.
      apply nth_safe_evi_indep.
    Qed.

    (** An existential restatement of [nth_safe_app] in terms of
        [app_lft] and [app_rht]. *)

    Lemma e_nth_safe_app : forall (l1 l2 : list A) (i : idx (l1 ++ l2)),
        (exists i1, nth_safe (l1 ++ l2) i = nth_safe l1 i1 /\ i = app_lft l2 i1)
        \/ (exists i2, nth_safe (l1 ++ l2) i = nth_safe l2 i2 /\ i = app_rht l1 i2).
    Proof.
      intros. pose proof (nth_safe_app l1 l2 i).
      destruct H as [[H0 H1]|[H0 H1]].
      - left.
        exists (to_idx H0).
        split; auto.
        apply app_idx_lft.
      - right.
        pose proof (
            app_idx_rht_bnd _ _ _ H0
          ) as Hn'.
        exists (to_idx Hn').
        split; auto.
        apply app_idx_rht; auto.
    Qed.

    (** Since they are common in our use case, we extend
        [e_nth_safe_app] to appends of three and four lists. *)

    Corollary e_nth_safe_app_3 :
      forall (l1 l2 l3 : list A) (i : idx (l1 ++ l2 ++ l3)),
        (exists i1, nth_safe (l1 ++ l2 ++ l3) i = nth_safe l1 i1
                    /\ i = app_lft (l2 ++ l3) i1)
        \/ (exists i2, nth_safe (l1 ++ l2 ++ l3) i = nth_safe l2 i2
                       /\ i = app_rht l1 (app_lft l3 i2))
        \/ (exists i3, nth_safe (l1 ++ l2 ++ l3) i = nth_safe l3 i3
                       /\ i = app_rht l1 (app_rht l2 i3)).
    Proof.
      intros.
      pose proof (e_nth_safe_app _ _ i).
      destruct H; auto. right.
      destruct H as [i' [H0 H1]].
      pose proof (e_nth_safe_app _ _ i').
      destruct H as [[i2 [H' H'']]|[i3 [H' H'']]];
        subst i'; rewrite H' in H0.
      - left. exists i2. auto.
      - right. exists i3. auto.
    Qed.

    Corollary e_nth_safe_app_4 :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1 ++ l2 ++ l3 ++ l4)),
        (exists i1, nth_safe (l1 ++ l2 ++ l3 ++ l4) i = nth_safe l1 i1
                    /\ i = app_lft (l2 ++ l3 ++ l4) i1)
        \/ (exists i2, nth_safe (l1 ++ l2 ++ l3 ++ l4) i = nth_safe l2 i2
                       /\ i = app_rht l1 (app_lft (l3 ++ l4) i2))
        \/ (exists i3, nth_safe (l1 ++ l2 ++ l3 ++ l4) i = nth_safe l3 i3
                       /\ i = app_rht l1 (app_rht l2 (app_lft l4 i3)))
        \/ (exists i4, nth_safe (l1 ++ l2 ++ l3 ++ l4) i = nth_safe l4 i4
                       /\ i = app_rht l1 (app_rht l2 (app_rht l3 i4))).
    Proof.
      intros.
      pose proof (e_nth_safe_app_3 _ _ _ i).
      destruct H as [H|[H|H]]; auto.
      right; right.
      destruct H as [i' [H0 H1]].
      pose proof (e_nth_safe_app _ _ i').
      destruct H as [[i3 [H' H'']]|[i4 [H' H'']]];
        subst i'; rewrite H' in H0.
      - left. exists i3. auto.
      - right. exists i4. auto.
    Qed.

  End AppLftRht.

  Section Splice.

    (** The splice operation: maps an [idx (l1 ++ l3)] to an [idx (l1
        ++ l2 ++ l3)]. *)

    Definition splc (l1 l2 l3 : list A) (i : idx (l1 ++ l3)) :
      idx (l1 ++ l2 ++ l3).
    Proof.
      (* Take cases on whether n < length l1 *)
      destruct i as [n Hn].
      rewrite app_length in Hn.
      destruct (le_le_S_dec (length l1) n).
      - (* length l1 <= n *)
        pose proof (nat_sub_lt _ _ _ Hn l).
        apply (app_rht l1 (app_rht l2 (@to_idx _ l3 (n - length l1) H))).
      - (* n < length l1 *)
        apply (app_lft (l2 ++ l3) (@to_idx _ l1 n l)).
    Defined.

    (** The next two results characterize the effect of [splc] on
        [idx_nat i]. *)

    Lemma idx_nat_splc_lft : forall (l1 l2 l3 : list A) (i : idx (l1 ++ l3)),
        idx_nat i < length l1 ->
        idx_nat (splc _ l2 _ i) = idx_nat i.
    Proof.
      intros.
      destruct i as [n Hn].
      simpl in *. destruct (
          le_le_S_dec (length l1) n
        ); simpl; lia.
    Qed.

    Lemma idx_nat_splc_rht : forall (l1 l2 l3 : list A) (i : idx (l1 ++ l3)),
        length l1 <= idx_nat i ->
        idx_nat (splc _ l2 _ i) = idx_nat i + length l2.
    Proof.
      intros.
      destruct i as [n Hn].
      simpl in *. destruct (
          le_le_S_dec (length l1) n
        ); simpl; lia.
    Qed.

    (** [splc] is injective. *)

    Lemma splc_inj : forall (l1 l2 l3 : list A), inj (@splc l1 l2 l3).
    Proof.
      unfold inj. intros. rewrite idx_eq_iff.
      rewrite idx_eq_iff in H.
      destruct (
          le_le_S_dec (length l1) (idx_nat a)
        );
        destruct (
            le_le_S_dec (length l1) (idx_nat a')
          ); [
          rewrite (idx_nat_splc_rht _ _ _ _ l) in H;
          rewrite (idx_nat_splc_rht _ _ _ _ l0) in H
        |
          rewrite (idx_nat_splc_rht _ _ _ _ l) in H;
          rewrite (idx_nat_splc_lft _ _ _ _ l0) in H
        |
          rewrite (idx_nat_splc_lft _ _ _ _ l) in H;
          rewrite (idx_nat_splc_rht _ _ _ _ l0) in H
        |
          rewrite (idx_nat_splc_lft _ _ _ _ l) in H;
          rewrite (idx_nat_splc_lft _ _ _ _ l0) in H
        ]; lia.
    Qed.

    (** [splc] preserves the result of [nth_safe]. *)

    Lemma splc_nth_safe : forall (l1 l2 l3 : list A) (i : idx (l1 ++ l3)),
        nth_safe (l1 ++ l2 ++ l3) (splc _ _ _ i) = nth_safe (l1 ++ l3) i.
    Proof.
      intros. unfold splc.
      destruct i as [n Hn].
      replace (
          (exist (fun n0 : nat => n0 < length (l1 ++ l3)) n Hn)
        ) with (to_idx Hn); auto.
      destruct (le_le_S_dec (length l1) n).
      - assert (H : n < length l1 + length l3).
        { rewrite app_length in Hn. assumption. }
        pose proof (nat_sub_lt _ _ _ H l).
        pose proof (
            nth_safe_app_rht l1 l3 (to_idx Hn) l
          ). simpl in H1.
        rewrite (H1 H0).
        repeat rewrite app_rht_nth_safe.
        apply nth_safe_evi_indep.
      - rewrite app_lft_nth_safe.
        rewrite (nth_safe_app_lft l1 l3 (to_idx Hn) l).
        reflexivity.
    Qed.

    (** Map an [idx (l1 ++ l2 ++ l4)] to an [idx (l1 ++ l2 ++ l3 ++ l4)]
        (left "cross splice" operation). *)

    Definition xsplc_lft (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l4)) :
      idx (l1++l2++l3++l4).
    Proof.
      (* We do not want to use [splc] in combination with [app_assoc]
      to define this.  Doing so renders Coq unable to completely
      simplify key graph operations later. *)
      destruct i as [n Hn].
      rewrite app_length in Hn.
      (* Take cases on whether n < length l1 *)
      destruct (le_le_S_dec (length l1) n) as [Hl|Hr].
      - (* length l1 <= n *)
        pose proof (nat_sub_lt _ _ _ Hn Hl) as H.
        (* Using [splc] in this way will not cause problems *)
        apply (app_rht l1 (splc l2 l3 l4 (to_idx H))).
      - (* n < length l1 *)
        apply (app_lft (l2 ++ l3 ++ l4) (to_idx Hr)).
    Defined.

    (** The next two results characterize the effect of [xsplc_lft] on
        [idx_nat i]. *)

    Lemma idx_nat_xsplc_lft_lft :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1 ++ l2 ++ l4)),
        idx_nat i < length l1 + length l2 ->
        idx_nat (xsplc_lft _ _ l3 _ i) = idx_nat i.
    Proof.
      intros. destruct i as [n Hn].
      simpl in *. destruct (
          le_le_S_dec (length l1) n
        ); try reflexivity.
      destruct (
          le_le_S_dec (length l2) (n - length l1)
        ); simpl; lia.
    Qed.

    Lemma idx_nat_xsplc_lft_rht :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1 ++ l2 ++ l4)),
        length l1 + length l2 <= idx_nat i ->
        idx_nat (xsplc_lft _ _ l3 _ i) = idx_nat i + length l3.
    Proof.
      intros. destruct i as [n Hn].
      simpl in *. destruct (
          le_le_S_dec (length l1) n
        ); try lia.
      destruct (
          le_le_S_dec (length l2) (n - length l1)
        ); simpl; lia.
    Qed.

    (** [xsplc_lft] is injective. *)

    Lemma xsplc_lft_inj :
      forall (l1 l2 l3 l4 : list A), inj (@xsplc_lft l1 l2 l3 l4).
    Proof.
      unfold inj. intros. rewrite idx_eq_iff.
      rewrite idx_eq_iff in H.
      destruct (
          le_le_S_dec (length l1 + length l2) (idx_nat a)
        );
        destruct (
            le_le_S_dec (length l1 + length l2) (idx_nat a')
          ); [
          rewrite (idx_nat_xsplc_lft_rht _ _ _ _ _ l) in H;
          rewrite (idx_nat_xsplc_lft_rht _ _ _ _ _ l0) in H
        |
          rewrite (idx_nat_xsplc_lft_rht _ _ _ _ _ l) in H;
          rewrite (idx_nat_xsplc_lft_lft _ _ _ _ _ l0) in H
        |
          rewrite (idx_nat_xsplc_lft_lft _ _ _ _ _ l) in H;
          rewrite (idx_nat_xsplc_lft_rht _ _ _ _ _ l0) in H
        |
          rewrite (idx_nat_xsplc_lft_lft _ _ _ _ _ l) in H;
          rewrite (idx_nat_xsplc_lft_lft _ _ _ _ _ l0) in H
        ]; lia.
    Qed.

    (** [xsplc_lft] preserves the result of [nth_safe]. *)

    Lemma xsplc_lft_nth_safe :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l4)),
        nth_safe (l1++l2++l3++l4) (xsplc_lft _ _ _ _ i) = nth_safe (l1++l2++l4) i.
    Proof.
      intros. unfold xsplc_lft.
      destruct i as [n Hn].
      replace (
          (exist (fun n0 : nat => n0 < length (l1 ++ l2 ++ l4)) n Hn)
        ) with (to_idx Hn); auto.
      destruct (le_le_S_dec (length l1) n).
      - assert (H : n < length l1 + length (l2 ++ l4)).
        { rewrite app_length in Hn. assumption. }
        pose proof (nat_sub_lt _ _ _ H l).
        pose proof (
            nth_safe_app_rht l1 (l2 ++ l4) (to_idx Hn) l
          ). simpl in H1.
        rewrite (H1 H0).
        rewrite app_rht_nth_safe.
        rewrite splc_nth_safe.
        apply nth_safe_evi_indep.
      - rewrite app_lft_nth_safe.
        rewrite (nth_safe_app_lft l1 (l2 ++ l4) (to_idx Hn) l).
        reflexivity.
    Qed.

    (** Map an [idx (l1 ++ l3 ++ l4)] to an [idx (l1 ++ l2 ++ l3 ++ l4)]
        (right cross splice operation). *)

    Definition xsplc_rht (l1 l2 l3 l4 : list A) (i : idx (l1++l3++l4)) : idx (l1++l2++l3++l4) :=
      splc l1 l2 (l3 ++ l4) i.

    (** The next two results characterize the effect of [xsplc_rht] on
        [idx_nat i]. *)

    Lemma idx_nat_xsplc_rht_lft :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1 ++ l3 ++ l4)),
        idx_nat i < length l1 ->
        idx_nat (xsplc_rht _ l2 _ _ i) = idx_nat i.
    Proof.
      intros. apply idx_nat_splc_lft. auto.
    Qed.

    Lemma idx_nat_xsplc_rht_rht :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1 ++ l3 ++ l4)),
        length l1 <= idx_nat i ->
        idx_nat (xsplc_rht _ l2 _ _ i) = idx_nat i + length l2.
    Proof.
      intros. apply idx_nat_splc_rht. auto.
    Qed.

    (** [xsplc_rht] is injective. *)

    Lemma xsplc_rht_inj :
      forall (l1 l2 l3 l4 : list A), inj (@xsplc_rht l1 l2 l3 l4).
    Proof.
      intros. apply splc_inj.
    Qed.

    (** [xsplc_rht] preserves the result of [nth_safe] *)

    Lemma xsplc_rht_nth_safe :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1++l3++l4)),
        nth_safe (l1++l2++l3++l4) (xsplc_rht _ _ _ _ i)
        = nth_safe (l1++l3++l4) i.
    Proof.
      intros. apply splc_nth_safe.
    Qed.

    (** A [xsplc_lft] only equals a [xsplc_rht] when both indices are
        derived from a common index of the first or last list. *)

    Lemma xsplc_lft_eq_rht :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l4)) (i' : idx (l1++l3++l4)),
        xsplc_lft l1 l2 l3 l4 i = xsplc_rht l1 l2 l3 l4 i' ->
        (exists (j : idx l1), i = app_lft (l2 ++ l4) j
                              /\ i' = app_lft (l3 ++ l4) j)
        \/ (exists (j : idx l4), i = app_rht l1 (app_rht l2 j)
                                 /\ i' = app_rht l1 (app_rht l3 j)).
    Proof.
      (* Take cases on ranges of [idx_nat] to use previous results *)
      intros. rewrite idx_eq_iff in H.
      destruct (
          le_le_S_dec (length l1 + length l2) (idx_nat i)
        ) as [Hl|Hl];
        destruct (le_le_S_dec (length l1) (idx_nat i')) as [Hr|Hr].
      - (* i in l4, i' in l3 ++ l4 *)
        rewrite idx_nat_xsplc_lft_rht in H; auto.
        rewrite idx_nat_xsplc_rht_rht in H; auto.
        (* Take cases on idx_nat i' - length l1 < length l3 *)
        pose proof (app_idx_rht_bnd _ _ _ Hr).
        destruct (
            le_le_S_dec (length l3) (idx_nat (to_idx H0))
          ) as [H1|H1].
        + (* i' in l4 *)
          pose proof (app_idx_rht_bnd _ _ _ H1).
          simpl in H2. right. exists (to_idx H2).
          split; rewrite idx_eq_iff;
            repeat rewrite idx_nat_app_rht; simpl; lia.
        + (* i' in l3 (contradiction) *)
          simpl in H1. lia.
      - (* i in l4, i' in l1 (contradiction) *)
        rewrite idx_nat_xsplc_lft_rht in H; auto.
        rewrite idx_nat_xsplc_rht_lft in H; auto. lia.
      - (* i in l1 ++ l2, i' in l3 ++ l4 (contradiction) *)
        rewrite idx_nat_xsplc_lft_lft in H; auto.
        rewrite idx_nat_xsplc_rht_rht in H; auto. lia.
      - (* i in l1 ++ l2, i' in l1 *)
        rewrite idx_nat_xsplc_lft_lft in H; auto.
        rewrite idx_nat_xsplc_rht_lft in H; auto.
        left. exists (to_idx Hr).
        split; rewrite idx_eq_iff;
          rewrite idx_nat_app_lft; simpl; auto.
    Qed.

    (** A restatement of [e_nth_safe_app_4] in terms of [xsplc_lft]
        and [xsplc_rht]. *)

    Lemma e_nth_safe_xsplc :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l3++l4)),
        (exists il, nth_safe (l1++l2++l3++l4) i = nth_safe (l1++l2++l4) il
                    /\ i = xsplc_lft _ _ _ _ il)
        \/ (exists ir, nth_safe (l1++l2++l3++l4) i = nth_safe (l1++l3++l4) ir
                       /\ i = xsplc_rht _ _ _ _ ir).
    Proof.
      intros.
      pose proof (e_nth_safe_app_4 _ _ _ _ i).
      destruct H as [[i1 [H0 H1]]|[[i2 [H0 H1]]|[[i3 [H0 H1]]|[i4 [H0 H1]]]]].
      (* It is slightly easier to deal with xsplc_rht, so we favor the
         right branch in cases where either would work (first and last) *)
      - right. exists (
            app_lft (l3 ++ l4) i1
          ). split.
        + rewrite H0.
          rewrite app_lft_nth_safe.
          reflexivity.
        + rewrite H1. rewrite idx_eq_iff.
          pose proof (idx_nat_lt_length i1).
          rewrite idx_nat_xsplc_rht_lft;
            repeat rewrite idx_nat_app_lft; lia.
      - left. exists (
            app_rht l1 (app_lft l4 i2)
          ). split.
        + rewrite H0.
          rewrite app_rht_nth_safe.
          rewrite app_lft_nth_safe.
          reflexivity.
        + rewrite H1. rewrite idx_eq_iff.
          pose proof (idx_nat_lt_length i2).
          rewrite idx_nat_xsplc_lft_lft;
            repeat rewrite idx_nat_app_rht;
            repeat rewrite idx_nat_app_lft; lia.
      - right. exists (
            app_rht l1 (app_lft l4 i3)
          ). split.
        + rewrite H0.
          rewrite app_rht_nth_safe.
          rewrite app_lft_nth_safe.
          reflexivity.
        + rewrite H1. rewrite idx_eq_iff.
          rewrite idx_nat_xsplc_rht_rht;
            repeat rewrite idx_nat_app_rht;
            repeat rewrite idx_nat_app_lft; lia.
      - right. exists (
            app_rht l1 (app_rht l3 i4)
          ). split.
        + rewrite H0.
          repeat rewrite app_rht_nth_safe.
          reflexivity.
        + rewrite H1. rewrite idx_eq_iff.
          rewrite idx_nat_xsplc_rht_rht;
            repeat rewrite idx_nat_app_rht; lia.
    Qed.

  End Splice.

  Section Swap.

    (** The inner swap operation: maps an [idx (l1 ++ l2 ++ l3 ++ l4)]
        to an [idx (l1 ++ l3 ++ l2 ++ l4)].

        This operation allows us to exploit symmetry in the Split-Join
        graph construction. *)

    Definition iswp (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l3++l4)) :
      idx (l1++l3++l2++l4).
    Proof.
      destruct i as [n Hn].
      destruct (
          le_le_S_dec (length l1) n
        ) as [H0|H0].
      - (* length l1 <= n *)
        rewrite app_length in Hn.
        pose proof (nat_sub_lt _ _ _ Hn H0) as Hn'.
        destruct (
            le_le_S_dec (length l2) (n - length l1)
          ) as [H1|H1].
        + (* length l2 <= n - length l1 *)
          rewrite app_length in Hn'.
          pose proof (nat_sub_lt _ _ _ Hn' H1) as Hn''.
          destruct (
              le_le_S_dec (length l3) (n - length l1 - length l2)
            ) as [H2|H2].
          * (* length l3 <= n - length l1 - length l2 *)
            rewrite app_length in Hn''.
            pose proof (nat_sub_lt _ _ _ Hn'' H2) as Hn'''.
            apply (app_rht l1 (app_rht l3 (app_rht l2 (to_idx Hn''')))).
          * (* n - length l1 - length l2 < length l3 *)
            apply (app_rht l1 (app_lft (l2 ++ l4) (to_idx H2))).
        + (* n - length l1 < length l2 *)
          apply (app_rht l1 (app_rht l3 (app_lft l4 (to_idx H1)))).
      - (* n < length l1 *)
        apply (app_lft (l3 ++ l2 ++ l4) (to_idx H0)).
    Defined.

    (** The next four results characterize the effect of [iswp] on
        [idx_nat]. *)

    Lemma idx_nat_iswp1 :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l3++l4)),
        idx_nat i < length l1 ->
        idx_nat (iswp l1 l2 l3 l4 i) = idx_nat i.
    Proof.
      intros. destruct i as [n Hn].
      unfold iswp; destruct (
          le_le_S_dec (length l1) n
        ); try (simpl in H; lia); auto.
    Qed.

    Lemma idx_nat_iswp2 :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l3++l4)),
        length l1 <= idx_nat i < length l1 + length l2 ->
        idx_nat (iswp l1 l2 l3 l4 i) = idx_nat i + length l3.
    Proof.
      intros l1 l2 l3 l4 i [H0 H1].
      unfold iswp;
        destruct i as [n Hn];
        simpl in H0, H1.
      destruct (
          le_le_S_dec (length l1) n
        ); try lia.
      destruct (
          le_le_S_dec (length l2) (n - length l1)
        ); simpl; lia.
    Qed.

    Lemma idx_nat_iswp3 :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l3++l4)),
        length l1 + length l2 <= idx_nat i < length l1 + length l2 + length l3 ->
        idx_nat (iswp l1 l2 l3 l4 i) = idx_nat i - length l2.
    Proof.
      intros l1 l2 l3 l4 i [H0 H1].
      unfold iswp;
        destruct i as [n Hn];
        simpl in H0, H1.
      destruct (
          le_le_S_dec (length l1) n
        ); try lia.
      destruct (
          le_le_S_dec (length l2) (n - length l1)
        ); try lia.
      destruct (
          le_le_S_dec (length l3) (n - length l1 - length l2)
        ); simpl; lia.
    Qed.

    Lemma idx_nat_iswp4 :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l3++l4)),
        length l1 + length l2 + length l3 <= idx_nat i ->
        idx_nat (iswp l1 l2 l3 l4 i) = idx_nat i.
    Proof.
      intros. unfold iswp;
        destruct i as [n Hn];
        simpl in H.
      destruct (
          le_le_S_dec (length l1) n
        ); try lia.
      destruct (
          le_le_S_dec (length l2) (n - length l1)
        ); try lia.
      destruct (
          le_le_S_dec (length l3) (n - length l1 - length l2)
        ); simpl; lia.
    Qed.

    (** Inner swap is injective. *)

    Lemma iswp_inj : forall (l1 l2 l3 l4 : list A), inj (@iswp l1 l2 l3 l4).
    Proof.
      unfold inj. intros. rewrite idx_eq_iff.
      rewrite idx_eq_iff in H.
      pose proof (app4_idx_nat_range _ _ _ _ a) as Hi.
      pose proof (app4_idx_nat_range _ _ _ _ a') as Hj.
      destruct Hi as [Hi|[Hi|[Hi|[Hi _]]]];
        destruct Hj as [Hj|[Hj|[Hj|[Hj _]]]];
        try rewrite (idx_nat_iswp1 _ _ _ _ _ Hi) in H;
        try rewrite (idx_nat_iswp2 _ _ _ _ _ Hi) in H;
        try rewrite (idx_nat_iswp3 _ _ _ _ _ Hi) in H;
        try rewrite (idx_nat_iswp4 _ _ _ _ _ Hi) in H;
        try rewrite (idx_nat_iswp1 _ _ _ _ _ Hj) in H;
        try rewrite (idx_nat_iswp2 _ _ _ _ _ Hj) in H;
        try rewrite (idx_nat_iswp3 _ _ _ _ _ Hj) in H;
        try rewrite (idx_nat_iswp4 _ _ _ _ _ Hj) in H; lia.
    Qed.

    (* Inner swap is its own inverse. *)

    Lemma iswp_inv : forall (l1 l2 l3 l4 : list A) (i : idx (l1++l2++l3++l4)),
        iswp l1 l3 l2 l4 (iswp l1 l2 l3 l4 i) = i.
    Proof.
      intros. rewrite idx_eq_iff.
      pose proof (app4_idx_nat_range _ _ _ _ (iswp l1 l2 l3 l4 i)).
      pose proof (app4_idx_nat_range _ _ _ _ i).
      destruct H as [H|[H|[H|[H _]]]];
        destruct H0 as [H0|[H0|[H0|[H0 _]]]];
        try rewrite (idx_nat_iswp1 _ _ _ _ _ H);
        try rewrite (idx_nat_iswp2 _ _ _ _ _ H);
        try rewrite (idx_nat_iswp3 _ _ _ _ _ H);
        try rewrite (idx_nat_iswp4 _ _ _ _ _ H);
        try rewrite (idx_nat_iswp1 _ _ _ _ _ H0) in *;
        try rewrite (idx_nat_iswp2 _ _ _ _ _ H0) in *;
        try rewrite (idx_nat_iswp3 _ _ _ _ _ H0) in *;
        try rewrite (idx_nat_iswp4 _ _ _ _ _ H0) in *;
        lia.
    Qed.

    Lemma iswp_inv_map : forall (l1 l2 l3 l4 : list A) pi,
        map (iswp l1 l3 l2 l4) (map (iswp l1 l2 l3 l4) pi) = pi.
    Proof.
      induction pi; simpl; auto.
      f_equal; auto; apply iswp_inv.
    Qed.

    (** The remaining lemmas characterize the relationship among
        [iswp], [xsplc_lft] and [xsplc_rht]. *)

    Lemma xsplc_lft_iswp_rht :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1 ++ l3 ++ l4)),
        xsplc_lft l1 l3 l2 l4 i = iswp l1 l2 l3 l4 (xsplc_rht l1 l2 l3 l4 i).
    Proof.
      intros. rewrite idx_eq_iff.
      pose proof (app3_idx_nat_range _ _ _ i).
      destruct H as [H|[H|H]].
      - rewrite idx_nat_xsplc_lft_lft; try lia.
        rewrite idx_nat_iswp1;
          rewrite idx_nat_xsplc_rht_lft; auto.
      - rewrite idx_nat_xsplc_lft_lft; try lia.
        rewrite idx_nat_iswp3;
          rewrite idx_nat_xsplc_rht_rht; lia.
      - rewrite idx_nat_xsplc_lft_rht; try lia.
        rewrite idx_nat_iswp4;
          rewrite idx_nat_xsplc_rht_rht; lia.
    Qed.

    Lemma xsplc_rht_iswp_lft :
      forall (l1 l2 l3 l4 : list A) (i : idx (l1 ++ l2 ++ l4)),
        xsplc_rht l1 l3 l2 l4 i = iswp l1 l2 l3 l4 (xsplc_lft l1 l2 l3 l4 i).
    Proof.
      intros. rewrite idx_eq_iff.
      pose proof (app3_idx_nat_range _ _ _ i).
      destruct H as [H|[H|H]].
      - rewrite idx_nat_xsplc_rht_lft; try lia.
        rewrite idx_nat_iswp1;
          rewrite idx_nat_xsplc_lft_lft; lia.
      - rewrite idx_nat_xsplc_rht_rht; try lia.
        rewrite idx_nat_iswp2;
          rewrite idx_nat_xsplc_lft_lft; lia.
      - rewrite idx_nat_xsplc_rht_rht; try lia.
        rewrite idx_nat_iswp4;
          rewrite idx_nat_xsplc_lft_rht; lia.
    Qed.

    Lemma iswp_eq_xsplc_lft : forall (l1 l2 l3 l4 : list A) i i',
        iswp l1 l2 l3 l4 i = xsplc_lft l1 l3 l2 l4 i' ->
        i = xsplc_rht l1 l2 l3 l4 i'.
    Proof.
      intros. rewrite idx_eq_iff in *.
      pose proof (app3_idx_nat_range _ _ _ i').
      pose proof (app4_idx_nat_range _ _ _ _ i).
      destruct H0 as [H0|[H0|[H0 _]]];
        destruct H1 as [H1|[H1|[H1|[H1 _]]]];
        try rewrite (idx_nat_iswp1 _ _ _ _ _ H1) in H;
        try rewrite (idx_nat_iswp2 _ _ _ _ _ H1) in H;
        try rewrite (idx_nat_iswp3 _ _ _ _ _ H1) in H;
        try rewrite (idx_nat_iswp4 _ _ _ _ _ H1) in H;
        try (rewrite idx_nat_xsplc_lft_lft in H; lia);
        try (rewrite idx_nat_xsplc_lft_rht in H; lia).
      - rewrite idx_nat_xsplc_lft_lft in H; try lia.
        rewrite idx_nat_xsplc_rht_lft; lia.
      - rewrite idx_nat_xsplc_lft_lft in H; try lia.
        rewrite idx_nat_xsplc_rht_rht; lia.
      - rewrite idx_nat_xsplc_lft_rht in H; try lia.
        rewrite idx_nat_xsplc_rht_rht; lia.
    Qed.

    Lemma iswp_eq_xsplc_lft_map : forall (l1 l2 l3 l4 : list A) pi' pi,
        map (iswp l1 l2 l3 l4) pi = map (xsplc_lft l1 l3 l2 l4) pi' ->
        pi = map (xsplc_rht l1 l2 l3 l4) pi'.
    Proof.
      induction pi'; simpl; intros.
      - eapply map_eq_nil. apply H.
      - destruct pi; simpl in H;
          try discriminate;
          injection H as H'.
        apply IHpi' in H.
        subst. f_equal.
        apply iswp_eq_xsplc_lft; auto.
    Qed.

  End Swap.

End AppInj.

Unset Implicit Arguments.
