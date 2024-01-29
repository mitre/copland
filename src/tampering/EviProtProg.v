(** The Copland Evidence Protection Program function adds signatures
    to a Copland phrase so that paths in the phrase's data flow
    semantics are protected.  It is idempotent, as we prove here. *)

(* LICENSE NOTICE

Copyright (c) 2023 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import FunInd Lia List.
Import ListNotations.

Require Import AllSet Copland DataFlow Evidence Graph Index Label Path Preamble Tamper TamperSet.

Definition plcs_subset_snglb := aset_subset_snglb String.string_dec.

(** * Definition 14: The [tau] function%\index{Definition 14: The $\tau$ function}% *)

Section Tau.

  (** The [tau] function computes the set of places that can modify
      evidence. *)

  Fixpoint tau (e : evi) : plcs :=
    match e with
    | ENul => plcs_empty
    | EMeas _ _ _ _ _ _ => plcs_all
    | ESig p e' =>
        plcs_inter (plcs_sngl p) (tau e')
    | EHsh _ e' => tau e'
    | ESeq e1 e2 =>
        plcs_union (tau e1) (tau e2)
    | EPar e1 e2 =>
        plcs_union (tau e1) (tau e2)
    end.

  (** Two evidence terms are equivalent if [tau] cannot distinguish
      them. *)

  Fixpoint evi_equiv (e1 e2 : evi) : Prop :=
    match e1, e2 with
    | ENul, ENul => True
    | EMeas _ _ _ _ _ _, EMeas _ _ _ _ _ _ => True
    | ESig p1 e1, ESig p2 e2 =>
        p1 = p2 /\ evi_equiv e1 e2
    | EHsh _ e1, EHsh _ e2 =>
        evi_equiv e1 e2
    | ESeq e1 e2, ESeq e1' e2' =>
        evi_equiv e1 e1' /\ evi_equiv e2 e2'
    | EPar e1 e2, EPar e1' e2' =>
        evi_equiv e1 e1' /\ evi_equiv e2 e2'
    | _, _ => False
    end.

  Functional Scheme evi_equiv_ind :=
    Induction for evi_equiv Sort Prop.

  (** All evidence is equivalent to itself. *)

  Lemma evi_equiv_refl : forall e, evi_equiv e e.
  Proof.
    intros; induction e; simpl; auto.
  Qed.

  (** Equivalent evidence cannot be distinguished by [tau]. *)

  Lemma tau_evi_equiv :
    forall e1 e2, evi_equiv e1 e2 -> tau e1 = tau e2.
  Proof.
    intros. functional induction (evi_equiv e1 e2);
      simpl; intuition; subst; auto;
      rewrite H; try rewrite H2; auto.
  Qed.

  (** The next two lemmas show that equivalence is preserved under
      [evi_lft] and [evi_rht] for any [splt]. *)

  Lemma evi_equiv_evi_lft :
    forall s e1 e2,
      evi_equiv e1 e2 ->
      evi_equiv (evi_lft s e1) (evi_lft s e2).
  Proof.
    unfold evi_lft; destruct s; simpl; auto.
  Qed.

  Lemma evi_equiv_evi_rht :
    forall s e1 e2,
      evi_equiv e1 e2 ->
      evi_equiv (evi_rht s e1) (evi_rht s e2).
  Proof.
    unfold evi_rht; destruct s; simpl; auto.
  Qed.

  (** Evidence produced by a phrase is equivalent even when its
      position is different as long as the previous evidence is
      equivalent. *)

  Lemma evi_equiv_phrase_pos_irrel :
    forall t p ps1 ps2 e1 e2,
      evi_equiv e1 e2 ->
      evi_equiv (phrase_to_evi t p ps1 e1) (phrase_to_evi t p ps2 e2).
  Proof.
    induction t; intros; simpl; auto.
    destruct b; simpl; split;
      try apply IHt1;
      try apply IHt2;
      try apply evi_equiv_evi_lft;
      try apply evi_equiv_evi_rht;
      auto.
  Qed.

  (** Function [tau] applied to evidence produced by a phrase is
      equivalent even when its position is different as long as the
      previous evidence is equivalent. *)

  Lemma tau_phrase_pos_irrel :
    forall t p ps1 ps2 e1 e2,
      evi_equiv e1 e2 ->
      tau (phrase_to_evi t p ps1 e1) = tau (phrase_to_evi t p ps2 e2).
  Proof.
    intros.
    apply tau_evi_equiv.
    apply evi_equiv_phrase_pos_irrel.
    assumption.
  Qed.

End Tau.

(** * Lemma 3%\index{Lemma 3}% *)

Section Lem23.

  (** For a [rev_coherent] path ending in a measurement event, the
      tamper set is a subset of [tau] applied to the endpoint's
      evidence. *)

  Lemma tmpr_set_subset_tau :
    forall [l : lbls] (pi : evt_seq l) v (p : plc),
      meas_lst (v :: pi) ->
      rev_coherent (v :: pi) ->
      plcs_mem p (tmpr_set (v :: pi)) = true ->
      plcs_mem p (tau (proje (nth_safe l v))) = true.
  Proof.
    induction pi; intros v p H [H0 H1] H2.
    - assert (0 < length [v]) by (simpl; lia).
      pose proof (H0 (to_idx H3)); simpl in H4.
      apply meas_lst_sngl in H.
      destruct H as [p' [msr [q [tgt [ps [e H]]]]]].
      rewrite H in *. simpl in H4.
      destruct e; try discriminate. auto.
    - apply meas_lst_cons_iff in H as H'.
      apply valid_lbl_seq_cons in H0 as H0'.
      apply rev_evi_passing_seq_cons in H1 as H1'.
      apply tmpr_set_weakly_decreasing_step in H2 as H2'.
      pose proof (IHpi _ _ H' (conj H0' H1') H2').
      assert (0 < length (v :: a :: pi)) by (simpl; lia).
      assert (1 < length (v :: a :: pi)) by (simpl; lia).
      assert (valid_lbl (nth_safe l v)) by apply (H0 (to_idx H4)).
      assert (evi_passing (nth_safe l a) (nth_safe l v)). {
        replace v with (nth_safe _ (to_idx H4)); auto.
        replace a with (nth_safe _ (to_idx H5)); auto.
      }
      unfold valid_lbl in H6.
      destruct (sig_lblb (nth_safe l v)) eqn:Hv.
      + (* v is a signature event *)
        apply sig_lbl_reflect in Hv as Hv'.
        destruct Hv' as [p' [e Hv']].
        rewrite tmpr_set_sign in H2; auto.
        rewrite Hv' in *; simpl sendp in H2; simpl.
        apply aset_inter_mem in H2 as [H2 _].
        apply aset_mem_sngl in H2 as H2''. subst p'.
        destruct e; simpl in H6; try discriminate.
        apply String.eqb_eq in H6; subst p0.
        destruct H7 as [H7|H7];
          rewrite <- H7 in H3; simpl in H3;
          apply aset_inter_mem; auto.
      + (* v is not a signature event *)
        destruct (nth_safe l v);
          destruct H7 as [H7|H7]; rewrite <- H7 in H3;
          destruct e; try destruct b;
          simpl in *; try discriminate; auto;
          try apply aset_union_mem; auto.
  Qed.

End Lem23.

(** * Lemma 4%\index{Lemma 4}% *)

Section Lem24.

  (** A [rev_coherent] IO graph is protected whenever [tau] of the
      label evidence of every cross-place communication event in the
      graph is a subset the singleton containing just the event's
      sending place. *)

  Lemma xplc_comm_tau_prot :
    forall (l : lbls) (G : io_graph l),
      rev_coherent_graph G ->
      (forall (v : io_evt G),
          xplc_comm_lbl (io_evt_lbl v) ->
          (forall p,
              plcs_mem p (tau (proje (io_evt_lbl v))) = true ->
              plcs_mem p (plcs_sngl (sendp (io_evt_lbl v))) = true)) ->
      prot_graph G.
  Proof.
    unfold prot_graph; intros.
    induction H1.
    - apply meas_lst_sngl in H2. constructor; auto.
    - destruct (xplc_comm_lblb (nth_safe l v)) eqn:H';
        apply meas_lst_cons_conv in H2 as H2';
        try (intro; discriminate);
        apply IHrev_path in H2' as H2''.
      + rewrite <- xplc_comm_lbl_reflect in H'.
        apply prot_xplc; auto.
        pose proof (H0 v H') as H''.
        assert (
            forall p,
              plcs_mem p (tmpr_set (v' :: pi)) = true ->
              plcs_mem p (tau (proje (nth_safe l v'))) = true
          ) by (intros; eapply tmpr_set_subset_tau; eauto).
        assert (evi_passing (nth_safe l v') (nth_safe l v)). {
          assert (io_rev_path G [v; v']) by (constructor; auto).
          apply H in H5 as [_ H5]; unfold rev_evi_passing_seq in H5.
          assert (0 < length [v; v']) by (simpl; lia).
          assert (1 < length [v; v']) by (simpl; lia).
          apply (H5 (to_idx H6) (to_idx H7)). reflexivity.
        }
        pose proof (xplc_comm_is_comm _ H').
        assert (
            tau (proje (nth_safe l v')) = tau (proje (nth_safe l v))
          ). {
          unfold evi_passing in H5.
          destruct H6 as [[p [q [e H6]]]|[q [p [e H6]]]];
            destruct H5; rewrite <- H5; rewrite H6; reflexivity.
        }
        rewrite H7 in *. auto.
      + apply Bool.not_true_iff_false in H'.
        rewrite <- xplc_comm_lbl_reflect in H'.
        apply prot_rest; auto.
  Qed.

End Lem24.

(** * Definition 15: Evidence Protection Program%\index{Definition 15: Evidence Protection Program}% *)

Section EviProtProg.

  Fixpoint evi_prot_prog (t : phrase) (p : plc) (e : evi) : phrase :=
    match t with
    | At q t' =>
        if String.string_dec p q then
          At p (evi_prot_prog t' p e)
        else
          if plcs_subset_snglb (tau e) p then
            let t1 := evi_prot_prog t' q e in
            if plcs_subset_snglb (tau (phrase_to_evi t1 q [] e)) q then
              At q t1
            else
              At q (Ln t1 Sig)
          else
            let t2 := evi_prot_prog t' q (ESig p e) in
            if plcs_subset_snglb (tau (phrase_to_evi t2 q [] (ESig p e))) q then
              Ln Sig (At q t2)
            else
              Ln Sig (At q (Ln t2 Sig))
    | Ln t1 t2 =>
        let t3 := evi_prot_prog t1 p e in
        Ln t3 (evi_prot_prog t2 p (phrase_to_evi t3 p [] e))
    | Br b s t1 t2 =>
        Br b s
          (evi_prot_prog t1 p (evi_lft s e))
          (evi_prot_prog t2 p (evi_rht s e))
    | _ => t
    end.

  (** The result of [evi_prot_prog] is the same when input evidence is
      replaced with equivalent evidence. *)

  Lemma evi_prot_prog_evi_equiv :
    forall t p e e',
      evi_equiv e e' ->
      evi_prot_prog t p e = evi_prot_prog t p e'.
  Proof.
    induction t; simpl; intros; auto.
    - destruct (String.string_dec p0 p).
      + erewrite IHt; eauto.
      + destruct (plcs_subset_snglb (tau e) p0) eqn:H0;
          destruct (plcs_subset_snglb (tau e') p0) eqn:H1.
        * destruct (
              plcs_subset_snglb (tau (phrase_to_evi (evi_prot_prog t p e) p [] e)) p
            ) eqn:H2;
            destruct (
                plcs_subset_snglb (tau (phrase_to_evi (evi_prot_prog t p e') p [] e')) p
              ) eqn:H3;
            try (erewrite IHt; eauto);
            erewrite IHt in H2; eauto;
            erewrite tau_phrase_pos_irrel in H2; eauto;
            rewrite H2 in H3; discriminate.
        * destruct (
              plcs_subset_snglb (tau (phrase_to_evi (evi_prot_prog t p e) p [] e)) p
            ) eqn:H2;
            destruct (
                plcs_subset_snglb
                  (tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e')) p [] (ESig p0 e')))
                  p
              ) eqn:H3;
            erewrite tau_evi_equiv in H0; eauto;
            rewrite H0 in H1; discriminate.
        * destruct (
              plcs_subset_snglb
                (tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e)))
                p
            ) eqn:H2;
            destruct (
                plcs_subset_snglb (tau (phrase_to_evi (evi_prot_prog t p e') p [] e')) p
              ) eqn:H3;
            erewrite tau_evi_equiv in H0; eauto;
            rewrite H0 in H1; discriminate.
        * assert (H': evi_equiv (ESig p0 e) (ESig p0 e')) by (simpl; intuition).
          destruct (
              plcs_subset_snglb
                (tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e)))
                p
            ) eqn:H2;
            destruct (
                plcs_subset_snglb
                  (tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e')) p [] (ESig p0 e')))
                  p
              ) eqn:H3;
            try (erewrite IHt; eauto);
            erewrite IHt in H2; eauto;
            erewrite tau_phrase_pos_irrel in H2; eauto;
            rewrite H2 in H3; discriminate.
    - erewrite IHt1; eauto.
      erewrite IHt2; eauto.
      apply evi_equiv_phrase_pos_irrel; auto.
    - assert (evi_equiv ENul ENul) by (simpl; auto).
      destruct b; destruct s; simpl; auto;
        try (erewrite IHt1; eauto);
        try (erewrite IHt2; eauto).
  Qed.

End EviProtProg.

(** * Theorem 4%\index{Theorem 4}% *)

Section Thm26.

  (** If [v] is a cross-place communication event in the data flow
      semantics of an [evi_prot_prog]-derived phrase, [tau] of [v]'s
      evidence is either empty or contains just [v]'s sending place. *)

  Theorem evi_prot_prog_xplc_subset :
    forall t p ps e (v : io_evt (phrase_to_flow (evi_prot_prog t p e) p ps e)),
      xplc_comm_lbl (io_evt_lbl v) ->
      tau (proje (io_evt_lbl v)) = plcs_empty
      \/ tau (proje (io_evt_lbl v)) = plcs_sngl (sendp (io_evt_lbl v)).
  Proof.
    unfold xplc_comm_lbl.
    induction t;
      try (
          simpl; intros;
          rewrite io_sngl_evt_lbl in H;
          simpl in H; contradiction
        ).
    - (* At *)
      simpl. intros p0 ps e.
      destruct (String.string_dec p0 p).
      + rewrite at_phrase_to_flow; intros.
        destruct (evt_lbl_bf_cpy _ _ v) as [[v' H']|[v' H']];
          assert (H0 : io_evt_lbl v = io_evt_lbl v') by (rewrite <- H'; auto); clear H'.
        * rewrite H0 in H. rewrite io_sngl_evt_lbl in H. simpl in H; contradiction.
        * destruct (evt_lbl_bf_cpy _ _ v') as [[u Hu]|[u Hu]];
            assert (H0' : io_evt_lbl v = io_evt_lbl u) by (rewrite <- Hu; auto);
            clear Hu; rewrite H0' in *.
          -- apply IHt in H. auto.
          -- rewrite io_sngl_evt_lbl in H; simpl in H; contradiction.
      + destruct (plcs_subset_snglb (tau e) p0) eqn:He;
          destruct (plcs_subset_snglb (tau (phrase_to_evi (evi_prot_prog t p e) p [] e)) p) eqn:He'.
        * rewrite at_phrase_to_flow; intros.
          destruct (evt_lbl_bf_cpy _ _ v) as [[v' H']|[v' H']];
            assert (H0 : io_evt_lbl v = io_evt_lbl v') by (rewrite <- H'; auto); clear H'.
          -- rewrite H0. rewrite io_sngl_evt_lbl. simpl. eapply aset_subset_snglb_cases; eauto.
          -- destruct (evt_lbl_bf_cpy _ _ v') as [[u Hu]|[u Hu]];
               assert (H0' : io_evt_lbl v = io_evt_lbl u) by (rewrite <- Hu; auto);
               clear Hu; rewrite H0' in *.
             ++ apply IHt in H. auto.
             ++ rewrite io_sngl_evt_lbl. simpl.
                rewrite (tau_phrase_pos_irrel _ _ _ [] e e); try apply evi_equiv_refl.
                eapply aset_subset_snglb_cases; eauto.
        * rewrite at_phrase_to_flow; intros.
          destruct (evt_lbl_bf_cpy _ _ v) as [[v' H']|[v' H']];
            assert (H0 : io_evt_lbl v = io_evt_lbl v') by (rewrite <- H'; auto); clear H'.
          -- rewrite H0. rewrite io_sngl_evt_lbl. simpl. eapply aset_subset_snglb_cases; eauto.
          -- simpl in v'. destruct (evt_lbl_bf_cpy _ _ v') as [[u Hu]|[u Hu]];
               assert (H0' : io_evt_lbl v = io_evt_lbl u) by (rewrite <- Hu; auto); clear Hu.
             ++ destruct (evt_lbl_bf_cpy _ _ u) as [[u' Hu']|[u' Hu']];
                  assert (H0'' : io_evt_lbl v = io_evt_lbl u') by (rewrite <- Hu'; auto);
                  clear Hu'; rewrite H0'' in *.
                ** apply IHt in H. auto.
                ** rewrite io_sngl_evt_lbl in H. contradiction.
             ++ rewrite H0'. rewrite io_sngl_evt_lbl. unfold sendp, proje, tau.
                rewrite (tau_phrase_pos_irrel _ _ _ [] e e); try apply evi_equiv_refl.
                rewrite <- (aset_subset_snglb_cases String.string_dec _ p).
                apply aset_inter_sngl_subset_lft.
        * destruct (
              plcs_subset_snglb
                (tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e))) p
            ) eqn:He''.
          -- intros. destruct (evt_lbl_bf_cpy _ _ v) as [[v' H']|[v' H']];
               assert (H0 : io_evt_lbl v = io_evt_lbl v') by (rewrite <- H'; auto); clear H'.
             ++ rewrite H0. rewrite io_sngl_evt_lbl. simpl.
                rewrite <- (aset_subset_snglb_cases String.string_dec _ p0).
                apply aset_inter_sngl_subset_lft.
             ++ destruct (evt_lbl_bf_cpy _ _ v') as [[u Hu]|[u Hu]];
                  assert (H0' : io_evt_lbl v = io_evt_lbl u) by (rewrite <- Hu; auto); clear Hu.
                ** rewrite H0'. rewrite io_sngl_evt_lbl. simpl.
                   rewrite <- (aset_subset_snglb_cases String.string_dec _ p0).
                   apply aset_inter_sngl_subset_lft.
                ** destruct (evt_lbl_bf_cpy _ _ u) as [[u' Hu']|[u' Hu']];
                     assert (H0'' : io_evt_lbl v = io_evt_lbl u') by (rewrite <- Hu'; auto);
                     clear Hu'; rewrite H0'' in *.
                   --- apply IHt in H. auto.
                   --- rewrite io_sngl_evt_lbl. simpl.
                       rewrite (tau_phrase_pos_irrel _ _ _ [] _ (ESig p0 e)); try apply evi_equiv_refl.
                       rewrite <- (aset_subset_snglb_cases String.string_dec _ p). auto.
          -- intros. destruct (evt_lbl_bf_cpy _ _ v) as [[v' H']|[v' H']];
               assert (H0 : io_evt_lbl v = io_evt_lbl v') by (rewrite <- H'; auto); clear H'.
             ++ rewrite H0. rewrite io_sngl_evt_lbl. simpl.
                rewrite <- (aset_subset_snglb_cases String.string_dec _ p0).
                apply aset_inter_sngl_subset_lft.
             ++ destruct (evt_lbl_bf_cpy _ _ v') as [[u Hu]|[u Hu]];
                  assert (H0' : io_evt_lbl v = io_evt_lbl u) by (rewrite <- Hu; auto); clear Hu.
                ** rewrite H0'. rewrite io_sngl_evt_lbl. simpl.
                   rewrite <- (aset_subset_snglb_cases String.string_dec _ p0).
                   apply aset_inter_sngl_subset_lft.
                ** destruct (evt_lbl_bf_cpy _ _ u) as [[u' Hu']|[u' Hu']];
                     assert (H0'' : io_evt_lbl v = io_evt_lbl u') by (rewrite <- Hu'; auto); clear Hu'.
                   --- destruct (evt_lbl_bf_cpy _ _ u') as [[w Hw]|[w Hw]];
                         assert (H0''' : io_evt_lbl v = io_evt_lbl w) by (rewrite <- Hw; auto);
                         clear Hw; rewrite H0''' in *.
                       +++ apply IHt in H. auto.
                       +++ rewrite io_sngl_evt_lbl. simpl.
                           rewrite <- (aset_subset_snglb_cases String.string_dec _ p).
                           rewrite (tau_phrase_pos_irrel _ _ _ [] _ (ESig p0 e)); try apply evi_equiv_refl.
                           destruct (
                               tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e))
                             );
                             try destruct (ListSet.set_mem String.string_dec p s);
                             try apply aset_subset_snglb_refl; auto.
                   --- rewrite H0''. rewrite io_sngl_evt_lbl. simpl.
                       rewrite <- (aset_subset_snglb_cases String.string_dec _ p).
                       rewrite (tau_phrase_pos_irrel _ _ _ [] _ (ESig p0 e)); try apply evi_equiv_refl.
                       destruct (
                           tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e))
                         );
                         try destruct (ListSet.set_mem String.string_dec p s);
                         try apply aset_subset_snglb_refl; auto.
        * destruct (
              plcs_subset_snglb
                (tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e))) p
            ) eqn:He''.
          -- intros. destruct (evt_lbl_bf_cpy _ _ v) as [[v' H']|[v' H']];
               assert (H0 : io_evt_lbl v = io_evt_lbl v') by (rewrite <- H'; auto); clear H'.
             ++ rewrite H0. rewrite io_sngl_evt_lbl. simpl.
                rewrite <- (aset_subset_snglb_cases String.string_dec _ p0).
                apply aset_inter_sngl_subset_lft.
             ++ destruct (evt_lbl_bf_cpy _ _ v') as [[u Hu]|[u Hu]];
                  assert (H0' : io_evt_lbl v = io_evt_lbl u) by (rewrite <- Hu; auto); clear Hu.
                ** rewrite H0'. rewrite io_sngl_evt_lbl. simpl.
                   rewrite <- (aset_subset_snglb_cases String.string_dec _ p0).
                   apply aset_inter_sngl_subset_lft.
                ** destruct (evt_lbl_bf_cpy _ _ u) as [[u' Hu']|[u' Hu']];
                     assert (H0'' : io_evt_lbl v = io_evt_lbl u') by (rewrite <- Hu'; auto);
                     clear Hu'; rewrite H0'' in *.
                   --- apply IHt in H. auto.
                   --- rewrite io_sngl_evt_lbl. simpl.
                       rewrite <- (aset_subset_snglb_cases String.string_dec _ p).
                       rewrite (tau_phrase_pos_irrel _ _ _ [] _ (ESig p0 e)); try apply evi_equiv_refl. auto.
          -- intros. destruct (evt_lbl_bf_cpy _ _ v) as [[v' H']|[v' H']];
               assert (H0 : io_evt_lbl v = io_evt_lbl v') by (rewrite <- H'; auto); clear H'.
             ++ rewrite H0. rewrite io_sngl_evt_lbl. simpl.
                rewrite <- (aset_subset_snglb_cases String.string_dec _ p0).
                apply aset_inter_sngl_subset_lft.
             ++ destruct (evt_lbl_bf_cpy _ _ v') as [[u Hu]|[u Hu]];
                  assert (H0' : io_evt_lbl v = io_evt_lbl u) by (rewrite <- Hu; auto); clear Hu.
                ** rewrite H0'. rewrite io_sngl_evt_lbl. simpl.
                   rewrite <- (aset_subset_snglb_cases String.string_dec _ p0).
                   apply aset_inter_sngl_subset_lft.
                ** destruct (evt_lbl_bf_cpy _ _ u) as [[u' Hu']|[u' Hu']];
                     assert (H0'' : io_evt_lbl v = io_evt_lbl u') by (rewrite <- Hu'; auto); clear Hu'.
                   --- destruct (evt_lbl_bf_cpy _ _ u') as [[w Hw]|[w Hw]];
                         assert (H0''' : io_evt_lbl v = io_evt_lbl w) by (rewrite <- Hw; auto);
                         clear Hw; rewrite H0''' in *.
                       +++ apply IHt in H. auto.
                       +++ rewrite io_sngl_evt_lbl. simpl.
                           rewrite <- (aset_subset_snglb_cases String.string_dec _ p).
                           rewrite (tau_phrase_pos_irrel _ _ _ [] _ (ESig p0 e)); try apply evi_equiv_refl.
                           destruct (
                               tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e))
                             );
                             try destruct (ListSet.set_mem String.string_dec p s);
                             try apply aset_subset_snglb_refl; auto.
                   --- rewrite H0''. rewrite io_sngl_evt_lbl. simpl.
                       rewrite <- (aset_subset_snglb_cases String.string_dec _ p).
                       rewrite (tau_phrase_pos_irrel _ _ _ [] _ (ESig p0 e)); try apply evi_equiv_refl.
                        destruct (
                           tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e))
                         );
                         try destruct (ListSet.set_mem String.string_dec p s);
                         try apply aset_subset_snglb_refl; auto.
    - (* Ln *)
      simpl; intros.
      destruct (evt_lbl_bf_cpy _ _ v) as [[v' H']|[v' H']]; rewrite H' in H.
      + apply IHt1 in H. rewrite <- H' in H; auto.
      + pose proof (
            evi_equiv_phrase_pos_irrel
              (evi_prot_prog t1 p e) p [] (0 :: ps) e e (evi_equiv_refl _)
          ).
        assert (
            evi_prot_prog t2 p (phrase_to_evi (evi_prot_prog t1 p e) p [] e) =
              evi_prot_prog t2 p (phrase_to_evi (evi_prot_prog t1 p e) p (0 :: ps) e)
          ). { apply evi_prot_prog_evi_equiv; auto. }
        generalize dependent v'; generalize dependent v; rewrite H1; intros.
        apply IHt2 in H. rewrite <- H' in H; auto.
    - (* Br *)
      simpl; intros.
      destruct (evt_lbl_splt_join_br v) as [[v' H']|[v' H']]; destruct s;
        try unfold splt_join_lft in v';
        try unfold splt_join_rht in v';
        try (destruct (evt_lbl_bf_cpy _ _ v') as [[u Hu]|[u Hu]]);
        try (destruct (evt_lbl_bf_nil _ _ v') as [[u Hu]|[u Hu]]);
        assert (H0 : io_evt_lbl v = io_evt_lbl u) by (rewrite <- Hu; auto);
        try (rewrite H0 in H; rewrite io_sngl_evt_lbl in H; simpl in H; contradiction);
        destruct (evt_lbl_bf_cpy _ _ u) as [[u' Hu']|[u' Hu']];
        assert (H0' : io_evt_lbl v = io_evt_lbl u') by (rewrite <- Hu'; auto);
        rewrite H0' in H; try (apply IHt1 in H); try (apply IHt2 in H);
        try (rewrite <- H0' in H); auto;
        rewrite H0' in H; rewrite io_sngl_evt_lbl in H; simpl in H; contradiction.
  Qed.

End Thm26.

(** * Corollary 1%\index{Corollary 1}% *)

Section Cor27.

  (** The [evi_prot_prog] function indeed protects Copland phrases,
      producing data flow semantics satisfying [protected_graph]. *)

  Theorem evi_prot_prog_protects :
    forall t p,
      protected_graph (copland_to_flow (p, evi_prot_prog t p ENul)).
  Proof.
    unfold copland_to_flow.
    simpl fst; simpl snd. intros.
    apply protected_graph_iff_prot_graph.
    apply xplc_comm_tau_prot.
    - apply coherent_graph_iff_rev_coherent_graph.
      apply phrase_to_flow_coherent.
    - intros. pose proof (evi_prot_prog_xplc_subset _ _ _ _ v H).
      destruct H1; rewrite H1 in H0; try (simpl in H0; discriminate); auto.
  Qed.

End Cor27.

(** * Theorem 5%\index{Theorem 5}% *)

Section Thm28.

  (** The [evi_prot_prog] function is idempotent. *)

  Theorem evi_prot_prog_idempotent :
    forall t p e,
      evi_prot_prog (evi_prot_prog t p e) p e = evi_prot_prog t p e.
  Proof.
    induction t; simpl; intros;
      try (rewrite IHt1; rewrite IHt2); auto.
    destruct (String.string_dec p0 p); simpl.
    - destruct (String.string_dec p0 p0); try contradiction.
      rewrite IHt; auto.
    - destruct (plcs_subset_snglb (tau e) p0) eqn:H0; simpl.
      + destruct (
            plcs_subset_snglb
              (tau (phrase_to_evi (evi_prot_prog t p e) p [] e))
              p
          ) eqn:H1; simpl;
          destruct (String.string_dec p0 p); try contradiction.
        * rewrite IHt, H0, H1. reflexivity.
        * rewrite H0.
          pose proof (
              aset_inter_sngl_subset_lft
                String.string_dec p
                (tau (phrase_to_evi (evi_prot_prog (evi_prot_prog t p e) p e) p [0] e))
            ).
          destruct (
              tau (phrase_to_evi (evi_prot_prog (evi_prot_prog t p e) p e) p [0] e)
            ); simpl in *; [
              destruct (String.string_dec p p); try contradiction |
              rewrite H
            ]; rewrite IHt; auto.
      + pose proof (
              aset_inter_sngl_subset_lft String.string_dec p0 (tau e)
            ).
        destruct (
            plcs_subset_snglb
              (tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e)))
              p
          ) eqn:H1; simpl;
          destruct (String.string_dec p0 p); try contradiction.
        * destruct (tau e); simpl in *; [
              destruct (String.string_dec p0 p0); try contradiction |
              rewrite H
            ];
            rewrite IHt, H1; reflexivity.
        * pose proof (
              aset_inter_sngl_subset_lft
                String.string_dec p
                (tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e)))
            ).
          destruct (tau e); simpl in *; [
              destruct (String.string_dec p0 p0); try contradiction |
              rewrite H
            ];
            rewrite IHt;
            rewrite (tau_phrase_pos_irrel _ _ _ [] _ (ESig p0 e));
            try apply evi_equiv_refl;
            destruct (
                tau (phrase_to_evi (evi_prot_prog t p (ESig p0 e)) p [] (ESig p0 e))
              ); simpl in *;
            try (destruct (String.string_dec p p); auto; contradiction);
            try (rewrite H2; auto).
  Qed.

End Thm28.
