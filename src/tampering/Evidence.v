(** Copland evidence semantics *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import List.
Import ListNotations.

Require Import Copland Graph.

(** * Basic definitions *)

Section EviVal.

  (** Positions in evidence *)

  Definition pos := list nat.

  (** Evidence values *)

  Inductive evi : Type :=
  | ENul
  | EMeas (msr : cmp) (q : plc) (tgt : cmp) (p : plc) (ps : pos) (e : evi)
  | ESig (p : plc) (e : evi)
  | EHsh (p : plc) (e : evi)
  | ESeq (e1 e2 : evi)
  | EPar (e1 e2 : evi).

  (** Returns the evidence input to an evidence value.

      Most evidence values take a single input, the exceptions being
      [ESeq] and [EPar], which take two.  To accommodate these,
      [evi_in] returns a pair of evidence values. *)

  Definition evi_in (e : evi) : evi * evi :=
    match e with
    | ENul => (ENul, ENul)
    | EMeas _ _ _ _ _ e => (e, e)
    | ESig _ e => (e, e)
    | EHsh _ e => (e, e)
    | ESeq e1 e2 => (e1, e2)
    | EPar e1 e2 => (e1, e2)
    end.

  (** Evidence subterm relation *)

  Inductive subterm (e : evi) : evi -> Prop :=
  | subterm_meas : forall msr q tgt p ps,
      subterm e (EMeas msr q tgt p ps e)
  | subterm_sig : forall p, subterm e (ESig p e)
  | subterm_hsh : forall p, subterm e (EHsh p e)
  | subterm_seq_l : forall e', subterm e (ESeq e e')
  | subterm_seq_r : forall e', subterm e (ESeq e' e)
  | subterm_par_l : forall e', subterm e (EPar e e')
  | subterm_par_r : forall e', subterm e (EPar e' e)
  | subterm_refl : subterm e e
  | subterm_trans : forall e' e'',
      subterm e e' -> subterm e' e'' -> subterm e e''.

End EviVal.

(** * Figure 3: Copland evidence semantics *)

Section EviCop.

  (** Compute the left branch input evidence for the given split. *)

  Definition evi_lft (s : splt) (e : evi) : evi :=
    match s with
    | Dup | Lft => e
    | _ => ENul
    end.

  (** Compute the right branch input evidence for the given split. *)

  Definition evi_rht (s : splt) (e : evi) : evi :=
    match s with
    | Dup | Rht => e
    | _ => ENul
    end.

  (** Compute the evidence semantics of a phrase. *)

  Fixpoint phrase_to_evi (t : phrase) (p : plc) (ps : pos) (e : evi) : evi :=
    match t with
    | Cpy => e
    | Meas msr q tgt => EMeas msr q tgt p ps e
    | Sig => ESig p e
    | Hsh => EHsh p e
    | At q t' => phrase_to_evi t' q (0 :: ps) e
    | Ln t1 t2 =>
        let e1 := phrase_to_evi t1 p (0 :: ps) e in
        phrase_to_evi t2 p (1 :: ps) e1
    | Br b s t1 t2 =>
        let e1 := phrase_to_evi t1 p (0 :: ps) (evi_lft s e) in
        let e2 := phrase_to_evi t2 p (1 :: ps) (evi_rht s e) in
        match b with
        | Seq => ESeq e1 e2
        | Par => EPar e1 e2
        end
    end.

End EviCop.

#[export]
 Hint Constructors subterm : core.
