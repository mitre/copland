(** Data flow event labels *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import Bool List PeanoNat String.
Import ListNotations.

Require Import Copland Evidence Graph Preamble.

Inductive lbl : Type :=
| LCpy (p : plc) (e : evi)
| LMsp (p : plc) (msr : cmp) (q : plc) (tgt : cmp) (ps : pos) (e : evi)
| LSig (p : plc) (e : evi)
| LHsh (p : plc) (e : evi)
| LReq (p q : plc) (e : evi)
| LRpy (q p : plc) (e : evi)
| LSplt (p : plc) (s : splt) (e : evi)
| LJoin (p : plc) (b : brch) (e : evi).

Definition lbls := list lbl.

(** * Definition 3: Place projections%\index{Definition 3: Place projections}% *)

Section PlcProj.

  Definition sendp (l : lbl) : plc :=
    match l with
    | LCpy p _ => p
    | LMsp p _ _ _ _ _ => p
    | LSig p _ => p
    | LHsh p _ => p
    | LReq p _ _ => p
    | LRpy q _ _ => q
    | LSplt p _ _ => p
    | LJoin p _ _ => p
    end.

  Definition recvp (l : lbl) : plc :=
    match l with
    | LCpy p _ => p
    | LMsp p _ _ _ _ _ => p
    | LSig p _ => p
    | LHsh p _ => p
    | LReq _ q _ => q
    | LRpy _ p _ => p
    | LSplt p _ _ => p
    | LJoin p _ _ => p
    end.

  (** The place-adjacency property for Copland event labels: the
      receiving place of the first label is the sending place of the
      second. *)

  Definition plc_adj (l l' : lbl) : Prop := recvp l = sendp l'.

End PlcProj.

(** * Definition 4: Cross-place communication%\index{Definition 4: Cross-place communication}% *)

Section XplcComm.

  (** Asserts that the given label's sending and receiving places are
      different.

      We prove separately that all [xplc_comm_lbl] are indeed
      [comm_lbl]. *)

  Definition xplc_comm_lbl (l : lbl) : Prop := sendp l <> recvp l.

  (** Boolean reflection of [xplc_comm_lbl] *)

  Definition xplc_comm_lblb (l : lbl) : bool :=
    negb (String.eqb (sendp l) (recvp l)).

  Lemma xplc_comm_lbl_reflect :
    forall l, xplc_comm_lbl l <-> xplc_comm_lblb l = true.
  Proof.
    unfold xplc_comm_lbl, xplc_comm_lblb; intros.
    pose proof String.eqb_spec (sendp l) (recvp l).
    destruct (String.eqb (sendp l) (recvp l));
      inv H; try rewrite H0; simpl; easy.
  Qed.

  (** A label is not a [xplc_comm_lbl] iff its sending and receiving
      places are equal. *)

  Lemma not_xplc_comm_lbl :
    forall l, ~ xplc_comm_lbl l <-> sendp l = recvp l.
  Proof.
    unfold xplc_comm_lbl; intro. apply plc_eq_dne.
  Qed.

End XplcComm.

(** * Definition 5: Label evidence projection%\index{Definition 5: Label evidence projection}% *)

Section EviProj.

  Definition proje (l : lbl) : evi :=
    match l with
    | LCpy _ e => e
    | LMsp _ _ _ _ _ e => e
    | LSig _ e => e
    | LHsh _ e => e
    | LReq _ _ e => e
    | LRpy _ _ e => e
    | LSplt _ _ e => e
    | LJoin _ _ e => e
    end.

  (** Project the input evidence from the label evidence. *)

  Definition proje_in (l : lbl) : evi * evi :=
    match l with
    | LCpy _ e => (e, e)
    | LMsp _ _ _ _ _ e => evi_in e
    | LSig _ e => evi_in e
    | LHsh _ e => evi_in e
    | LReq _ _ e => (e, e)
    | LRpy _ _ e => (e, e)
    | LSplt _ _ e => (e, e)
    | LJoin _ _ e => evi_in e
    end.

  (** The evidence-passing property for Copland event labels: the
      evidence in the first label is among the inputs to the evidence
      in the second. *)

  Definition evi_passing (l l' : lbl) : Prop :=
    fst (proje_in l') = proje l \/ snd (proje_in l') = proje l.

End EviProj.

(** * Properties of labels *)

Section LblProp.

  (** Asserts that the given label is for a measurement event. *)

  Definition meas_lbl (l : lbl) : Prop :=
    exists p msr q tgt ps e, l = LMsp p msr q tgt ps e.

  (** Boolean reflection of [meas_lbl] *)

  Definition meas_lblb (l : lbl) : bool :=
    match l with
    | LMsp _ _ _ _ _ _ => true
    | _ => false
    end.

  Lemma meas_lbl_reflect :
    forall l, meas_lbl l <-> meas_lblb l = true.
  Proof.
    unfold meas_lbl; split; intros.
    - destruct H as
        [p [msr [q [tgt [ps [e H]]]]]].
      subst; auto.
    - destruct l;
        try (simpl in H; discriminate).
      repeat eexists.
  Qed.

  (** For a [meas_lbl], [sendp] and [recvp] are equal. *)

  Lemma meas_lbl_sendp_eq_recvp :
    forall l, meas_lbl l -> sendp l = recvp l.
  Proof.
    intros l [p [msr [q [tgt [ps [e H]]]]]].
    subst; auto.
  Qed.

  (** Asserts that the given label is for a signature event. *)

  Definition sig_lbl (l : lbl) : Prop :=
    exists p e, l = LSig p e.

  (** Boolean reflection of [sig_lbl] *)

  Definition sig_lblb (l : lbl) : bool :=
    match l with
    | LSig _ _ => true
    | _ => false
    end.

  Lemma sig_lbl_reflect :
    forall l, sig_lbl l <-> sig_lblb l = true.
  Proof.
    unfold sig_lbl; split; intros.
    - destruct H as [p [e H]].
      subst; auto.
    - destruct l;
        try (simpl in H; discriminate).
      repeat eexists.
  Qed.

  (** For a [sig_lbl], [sendp] and [recvp] are equal. *)

  Lemma sig_lbl_sendp_eq_recvp :
    forall l, sig_lbl l -> sendp l = recvp l.
  Proof.
    intros l [p [e H]]; subst; auto.
  Qed.

  (** A signature label is not a measurement label. *)

  Lemma sig_lbl_neq_meas_lbl :
    forall l, sig_lbl l -> ~(meas_lbl l).
  Proof.
    unfold sig_lbl, meas_lbl.
    intros; intro.
    destruct H as [p [e H]].
    destruct H0 as [p' [msr [q [tgt [ps [e' H0]]]]]].
    subst; discriminate.
  Qed.

  (** A measurement label is not a signature label. *)

  Lemma meas_lbl_neq_sig_lbl :
    forall l, meas_lbl l -> ~(sig_lbl l).
  Proof.
    unfold meas_lbl, sig_lbl.
    intros; intro.
    destruct H as [p' [msr [q [tgt [ps [e' H]]]]]].
    destruct H0 as [p [e H0]].
    subst; discriminate.
  Qed.

  (** Asserts that the given label is for a request event. *)

  Definition req_lbl (l : lbl) : Prop :=
    exists p q e, l = LReq p q e.

  (** Boolean reflection of [req_lbl] *)

  Definition req_lblb (l : lbl) : bool :=
    match l with
    | LReq _ _ _ => true
    | _ => false
    end.

  Lemma req_lbl_reflect :
    forall l, req_lbl l <-> req_lblb l = true.
  Proof.
    unfold req_lbl; split; intros.
    - destruct H as [p [q [e H]]].
      subst; auto.
    - destruct l;
        try (simpl in H; discriminate).
      repeat eexists.
  Qed.

  (** Asserts that the given label is for a reply event. *)

  Definition rpy_lbl (l : lbl) : Prop :=
    exists q p e, l = LRpy q p e.

  (** Boolean reflection of [rpy_lbl] *)

  Definition rpy_lblb (l : lbl) : bool :=
    match l with
    | LRpy _ _ _ => true
    | _ => false
    end.

  Lemma rpy_lbl_reflect :
    forall l, rpy_lbl l <-> rpy_lblb l = true.
  Proof.
    unfold rpy_lbl; split; intros.
    - destruct H as [q [p [e H]]].
      subst; auto.
    - destruct l;
        try (simpl in H; discriminate).
      repeat eexists.
  Qed.

  (** Asserts that the given label is for a communication event, a
      request or reply. *)

  Definition comm_lbl (l : lbl) : Prop := req_lbl l \/ rpy_lbl l.

  (** Boolean reflection of [comm_lbl] *)

  Definition comm_lblb (l : lbl) : bool := req_lblb l || rpy_lblb l.

  Definition comm_lbl_reflect :
    forall l, comm_lbl l <-> comm_lblb l = true.
  Proof.
    unfold comm_lbl, comm_lblb; intros.
    rewrite req_lbl_reflect.
    rewrite rpy_lbl_reflect.
    split; intros.
    - destruct H; rewrite H; auto;
        apply Bool.orb_true_r.
    - apply orb_true_iff in H; auto.
  Qed.

  (** Every [xplc_comm_lbl] is indeed a [comm_lbl]. *)

  Lemma xplc_comm_is_comm :
    forall l, xplc_comm_lbl l -> comm_lbl l.
  Proof.
    intro l.
    rewrite xplc_comm_lbl_reflect.
    unfold xplc_comm_lblb.
    rewrite comm_lbl_reflect.
    destruct l; simpl; intros;
      try rewrite String.eqb_refl in H;
      try discriminate;
      reflexivity.
  Qed.

End LblProp.

(** * Valid label evidence *)

Section ValidLbl.

  (** Defines which evidence values are valid for each label. *)

  Definition valid_lblb (l : lbl) : bool :=
    match l with
    | LCpy _ _ => true
    | LMsp p msr q tgt ps (EMeas msr' q' tgt' p' ps' _) =>
        String.eqb p p' && String.eqb msr msr' && String.eqb q q'
        && String.eqb tgt tgt' && list_eqb Nat.eq_dec ps ps'
    | LSig p (ESig p' _) => String.eqb p p'
    | LHsh p (EHsh p' _) => String.eqb p p'
    | LReq _ _ _ => true
    | LRpy _ _ _ => true
    | LSplt _ _ _ => true
    | LJoin _ Seq (ESeq _ _) => true
    | LJoin _ Par (EPar _ _) => true
    | _ => false
    end.

  (** A propositional equivalent of [valid_lblb] *)

  Definition valid_lbl (l : lbl) : Prop := valid_lblb l = true.

End ValidLbl.
