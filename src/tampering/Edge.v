(** Edges are pairs of list indices. *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import List ListSet.
Import ListNotations.

Require Import Index Preamble.

Set Implicit Arguments.

(** * Basic definitions *)

Section EdgeDefn.

  Variable A : Type.
  Variable l : list A.

  Definition edge := (idx l * idx l) % type.

  (** Decidable equality of [edge] from that of [idx] *)

  Definition edge_eq_dec : forall (f f' : edge), {f = f'} + {f <> f'}.
  Proof.
    destruct f as [i j].
    destruct f' as [i' j'].
    destruct (idx_eq_dec i i');
      destruct (idx_eq_dec j j').
    - left. subst. reflexivity.
    - right. intro. injection H as H.
      apply n in H0. contradiction.
    - right. intro. injection H as H.
      apply n in H. contradiction.
    - right. intro. injection H as H.
      apply n in H. contradiction.
  Defined.

End EdgeDefn.

(** * Injecting [edge] through list appends *)

Section AppInj.

  Variable A : Type.

  (** Map an [idx l1] and an [idx l2] to an [edge (l1 ++ l2)]. *)

  Definition to_app_edge (l1 l2 : list A) (i1 : idx l1) (i2 : idx l2) :
    edge (l1 ++ l2) :=
    (app_lft l2 i1, app_rht l1 i2).

  (** Map an [edge l1] to an [edge (l1 ++ l2)]. *)

  Definition edge_app_lft (l1 l2 : list A) (f : edge l1) : edge (l1 ++ l2) :=
    map_pair (app_lft l2) f.

  (** Map an [edge l2] to an [edge (l1 ++ l2)]. *)

  Definition edge_app_rht (l1 l2 : list A) (f : edge l2) : edge (l1 ++ l2) :=
    map_pair (@app_rht _ l1 l2) f.

  (** Map an [edge (l1 ++ l2 ++ l4)] to an [edge (l1 ++ l2 ++ l3 ++ l4)]. *)

  Definition edge_xsplc_lft (l1 l2 l3 l4 : list A) (f : edge (l1++l2++l4)) :
    edge (l1++l2++l3++l4) :=
    map_pair (xsplc_lft l1 l2 l3 l4) f.

  (** Map an [edge (l1 ++ l3 ++ l4)] to an [edge (l1 ++ l2 ++ l3 ++ l4)]. *)

  Definition edge_xsplc_rht (l1 l2 l3 l4 : list A) (f : edge (l1++l3++l4)) :
    edge (l1++l2++l3++l4) :=
    map_pair (xsplc_rht l1 l2 l3 l4) f.

End AppInj.

(** * Sets of edges *)

Section EdgesDefn.

  Variable A : Type.
  Variable l : list A.

  Definition edges := set (edge l).

  Definition empty_edges := @empty_set (edge l).

  (** Add an [edge] to a set of edges. *)

  Definition edges_add := set_add (@edge_eq_dec A l).

  (** Set union *)

  Definition edges_union := set_union (@edge_eq_dec A l).

End EdgesDefn.

(** * Injecting [edges] through list appends. *)

Section EdgesAppInj.

  Variable A : Type.

  (** Map an [edges l1] to an [edges (l1 ++ l2)]. *)

  Definition edges_app_lft (l1 l2 : list A) (E : edges l1) :
    edges (l1 ++ l2) :=
    map (edge_app_lft l2) E.

  (** Map an [edges l2] to an [edges (l1 ++ l2)]. *)

  Definition edges_app_rht (l1 l2 : list A) (E : edges l2) :
    edges (l1 ++ l2) :=
    map (@edge_app_rht _ l1 l2) E.

  (** Map an [edges (l1 ++ l2 ++ l4)] into an [edges (l1 ++ l2 ++ l3 ++ l4)]. *)

  Definition edges_xsplc_lft (l1 l2 l3 l4 : list A) (E : edges (l1++l2++l4)) :
    edges (l1++l2++l3++l4) :=
    map (edge_xsplc_lft l1 l2 l3 l4) E.

  (** Map an [edges (l1 ++ l3 ++ l4)] into an [edges (l1 ++ l2 ++ l3 ++ l4)]. *)

  Definition edges_xsplc_rht (l1 l2 l3 l4 : list A) (E : edges (l1++l3++l4)) :
    edges (l1++l2++l3++l4) :=
    map (edge_xsplc_rht l1 l2 l3 l4) E.

End EdgesAppInj.

Unset Implicit Arguments.
