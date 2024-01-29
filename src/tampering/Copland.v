(** The Copland language *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import String.

Require Import Graph.

(** Places *)

Definition plc := string.

Lemma plc_eq_dne :
  forall (p p' : plc), ~ p <> p' <-> p = p'.
Proof.
  split; intros;
    destruct (String.string_dec p p');
    auto; contradiction.
Qed.

(** We can always find a place different from a given one. *)

Lemma plc_exists_neq :
  forall (p : plc), exists (q : plc), q <> p.
Proof.
  intros.
  destruct (string_dec p EmptyString); subst.
  - exists "p"%string. intro. discriminate.
  - eexists. eauto.
Qed.

(** Components, measurers and targets *)

Definition cmp := string.

(** Kinds of branch, sequential or parallel *)

Inductive brch : Type :=
| Seq
| Par.

(** Copland phrases *)

Inductive phrase : Type :=
| Cpy
| Meas (msr : cmp) (q : plc) (tgt : cmp)
| Sig
| Hsh
| At (p : plc) (t : phrase)
| Ln (t1 t2 : phrase)
| Br (b : brch) (s : splt) (t1 t2 : phrase).

(** Copland attestation specification, a [phrase] executing at a
    starting [plc] *)

Definition copland := (plc * phrase) % type.
