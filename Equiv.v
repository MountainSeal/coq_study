Require Export Imp.


Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) :=
  forall (st:state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st || st') <-> (c2 / st || st').

Theorem aequiv_example :
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
intros st. simpl. apply minus_diag.
Qed.

Theorem bequiv_example :
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

Theorem skip_left : forall c,
    cequiv (SKIP; c) c.
Proof.
  intros c st st'.
  split; intros H.
  Case "->".
    inversion H. subst.
    inversion H2. subst.
    assumption.
  Case "<-".
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

Theorem skip_right : forall c,
    cequiv (c; SKIP) c.
Proof.
  intros c st st'.
  split; intros H.
  Case "->".
    inversion H. subst.
    inversion H5. subst.
    assumption.
  Case "<-".
    apply E_Seq with st'.
    assumption.
    apply E_Skip.
Qed.

Theorem IFB_true_simple : forall c1 c2,
    cequiv
      (IFB BTrue THEN c1 ELSE c2 FI)
      c1.
Proof.
  intros c1 c2.
  split; intros H.
  Case "->".
    inversion H; subst. assumption. inversion H5.
  Case "<-".
    apply E_IfTrue. reflexivity. assumption.
Qed.

Theorem IFB_true : forall b c1 c2,
    bequiv b BTrue ->
    cequiv
      (IFB b THEN c1 ELSE c2 FI)
      c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true".
      assumption.
    SCase "b evaluates to false".
      rewrite Hb in H5.
      inversion H5.
  Case "<-".
    apply E_IfTrue; try assumption.
    rewrite Hb. reflexivity.
Qed.

Theorem IFB_false : forall b c1 c2,
    bequiv b BFalse ->
    cequiv (IFB b THEN c1 ELSE c2 FI)
           c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true".
      rewrite Hb in H5.
      inversion H5.
    SCase "b evaluates to false".
      assumption.
  Case "<-".
    apply E_IfFalse; try assumption.
    rewrite Hb. reflexivity.
Qed.

Theorem swap_if_branches : forall b e1 e2,
    cequiv
      (IFB b THEN e1 ELSE e2 FI)
      (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2 st st'.
  split; intros H.
  Case "->".
    inversion H; subst;
      [ apply E_IfFalse; simpl; try apply negb_false_iff
      | apply E_IfTrue; simpl; try apply negb_true_iff];
      assumption.
  Case "<-".
    inversion H; subst;
      [ apply E_IfFalse; simpl in H5; try apply negb_true_iff
      | apply E_IfTrue; simpl in H5; try apply negb_false_iff
      ];
      assumption.
Qed.

Theorem WHILE_false : forall b c,
    bequiv b BFalse ->
    cequiv
      (WHILE b DO c END)
      SKIP.
Proof.
  intros b c Hb. split; intros H.
  Case "->".
    inversion H; subst.
    SCase "E_WhileEnd".
      apply E_Skip.
    SCase "E_While_Loop".
      rewrite Hb in H2. inversion H2.
  Case "<-".
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity.
Qed.

Theorem WHILE_true_nonterm : forall b c st st',
    bequiv b BTrue ->
    ~((WHILE b DO c END) / st || st').
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw.
  ceval_cases (induction H) Case;
    inversion Heqcw; subst; clear Heqcw.
  Case "E_WhileEnd". rewrite Hb in H. inversion H.
  Case "E_WhileLoop". apply IHceval2. reflexivity.
Qed.

Theorem WHILE_true : forall b c,
    bequiv b BTrue ->
    cequiv
      (WHILE b DO c END)
      (WHILE BTrue DO SKIP END).
Proof.
  intros.
  split; intros.
  Case "->". apply WHILE_true_nonterm in H0.
    apply ex_falso_quodlibet. apply H0.
    apply H.
  Case "<-".
    apply WHILE_true_nonterm in H0.
    apply ex_falso_quodlibet. apply H0.
    unfold bequiv. intros. reflexivity.
Qed.

Theorem loop_unrolling : forall b c,
    cequiv
      (WHILE b DO c END)
      (IFB b THEN (c; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    SCase "loop doesn't run".
      apply E_IfFalse. assumption. apply E_Skip.
    SCase "loop runs".
     apply E_IfTrue. assumption.
     apply E_Seq with (st' := st'0). assumption. assumption.
  Case "<-".
    inversion Hce; subst.
    SCase "loop runs".
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    SCase "loop doesn't run".
      inversion H5; subst. apply E_WhileEnd. assumption.
Qed.

Theorem seq_assoc : forall c1 c2 c3,
    cequiv ((c1;c2);c3) (c1;(c2;c3)).
Proof.
  intros.
  split; intros H; inversion H; subst.
  Case "->".
    inversion H2; subst.
    apply E_Seq with (st' := st'1);
      [ assumption
      | apply E_Seq with (st' := st'0);
        assumption; assumption].
  Case "<-".
    inversion H5; subst.
    apply E_Seq with (st' := st'1).
    apply E_Seq with (st' := st'0).
    assumption. assumption. assumption.
Qed.

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y},
    (forall (x:X), f x = g x) -> f = g.

Theorem identity_assignment : forall (X:id),
    cequiv
      (X ::= AId X)
      SKIP.
Proof.
  intros. split; intro H.
  Case "->".
    inversion H; subst. simpl.
    replace (update st X (st X)) with st.
    constructor.
    apply functional_extensionality. intro.
    rewrite update_same; reflexivity.
  Case "<-".
    inversion H; subst.
    assert (st' = (update st' X (st' X))).
      apply functional_extensionality. intro.
      rewrite update_same; reflexivity.
    rewrite H0 at 2.
    constructor. reflexivity.
Qed.

Theorem assign_aequiv : forall X e,
    aequiv (AId X) e ->
    cequiv SKIP (X ::= e).
Proof.
  intros X e H. split; intro;
  inversion H0; subst.
  Case "->".
    assert (st' = (update st' X (aeval st' e))).
    SCase "proof of assertion".
      apply functional_extensionality. intro.
      rewrite update_same. reflexivity. apply H.
    rewrite H1 at 2. constructor. reflexivity.
  Case "<-".
    assert (st = (update st X (aeval st e))).
    SCase "proof of assertion".
      apply functional_extensionality. intro.
      rewrite update_same. reflexivity. apply H.
    rewrite H1 at 1. constructor.
Qed.

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
    aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.
Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
    aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.
Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  intros b st. reflexivity.
Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
    bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.
Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
    bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.
Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.
Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
    cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st || st' <-> c2 / st || st') as H'.
    SCase "Proof of assertion". apply H.
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
    (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
    cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st || st'). apply H12. apply H23.
Qed.

Theorem CAss_congruence : forall i a1 a1',
    aequiv a1 a1' ->
    cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  Case "->".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  Case "<-".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
    bequiv b1 b1' -> cequiv c1 c1' ->
    cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  Case "->".
    remember (WHILE b1 DO c1 END) as cwhile.
    induction Hce; inversion Heqcwhile; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite <- Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st'). apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.
  Case "<-".
    remember (WHILE b1' DO c1' END) as c'while.
    induction Hce; inversion Heqc'while; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite -> Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st'). apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
    cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (c1;c2) (c1';c2').
Proof.
  unfold cequiv.
  intros c1 c1' c2 c2' Hc1e Hc2e st st'.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    apply E_Seq with (st' := st'0).
      apply Hc1e. apply H1.
      apply Hc2e. apply H4.
  Case "<-".
    inversion Hce; subst.
    apply E_Seq with (st' := st'0).
      apply Hc1e. apply H1.
      apply Hc2e. apply H4.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv,cequiv.
  intros b b' c1 c1' c2 c2' Hbe Hc1e Hc2e st st'.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    SCase "E_IfTrue".
      apply E_IfTrue. rewrite -> (Hbe st) in H4. assumption.
      apply Hc1e. assumption.
    SCase "E_IfFalse".
      apply E_IfFalse. rewrite -> (Hbe st) in H4. assumption.
      apply Hc2e. assumption.
  Case "<-".
    inversion Hce; subst.
    SCase "E_IfTrue".
      apply E_IfTrue. rewrite <- (Hbe st) in H4. assumption.
      apply Hc1e. assumption.
    SCase "E_IfFalse".
      apply E_IfFalse. rewrite <- (Hbe st) in H4. assumption.
      apply Hc2e. assumption.
Qed.

Example congruence_example:
  cequiv
    (X ::= ANum 0;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (X ::= ANum 0;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
    apply refl_cequiv.
    apply CIf_congruence.
      apply refl_bequiv.
      apply CAss_congruence. unfold aequiv. simpl.
        symmetry. apply minus_diag.
      apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i  => AId i
  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
end.

Example fold_aexp_ex1 :
  fold_constants_aexp
    (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity.
Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp
    (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6)) (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity.
Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
    | (a1', a2') => BEq a1' a2'
    end
  | BLe a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => if ble_nat n1 n2 then BTrue else BFalse
    | (a1', a2') => BLe a1' a2'
    end
  | BNot b1 =>
    match (fold_constants_bexp b1) with
    | BTrue => BFalse
    | BFalse => BTrue
    | b1' => BNot b1'
    end
  | BAnd b1 b2 =>
    match (fold_constants_bexp b1, fold_constants_bexp b2) with
    | (BTrue, BTrue) => BTrue
    | (BTrue, BFalse) => BFalse
    | (BFalse, BTrue) => BFalse
    | (BFalse, BFalse) => BFalse
    | (b1', b2') => BAnd b1' b2'
    end
end.

Example fold_bexp_ex1 :
  fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity.
Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp
    (BAnd (BEq (AId X) (AId Y))
          (BEq (ANum 0)
               (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity.
Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP => SKIP
  | i ::= a => CAss i (fold_constants_aexp a)
  | c1 ; c2 =>
    (fold_constants_com c1) ; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
    match fold_constants_bexp b with
    | BTrue => fold_constants_com c1
    | BFalse => fold_constants_com c2
    | b' => IFB b' THEN fold_constants_com c1
                   ELSE fold_constants_com c2 FI
    end
  | WHILE b DO c END =>
    match fold_constants_bexp b with
    | BTrue => WHILE BTrue DO SKIP END
    | BFalse => SKIP
    | b' => WHILE b' DO (fold_constants_com c) END
    end
end.

Example fold_com_ex1 :
  fold_constants_com
    (X ::= APlus (ANum 4) (ANum 5);
     Y ::= AMinus (AId X) (ANum 3);
     IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;
     IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END) =
  (X ::= ANum 9;
   Y ::= AMinus (AId X) (ANum 3);
   IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
     SKIP
   ELSE
     (Y ::= ANum 0)
   FI;
   Y ::= ANum 0;
   WHILE BEq (AId Y) (ANum 0) DO
     X ::= APlus (AId X) (ANum 1)
   END).
Proof. reflexivity.
Qed.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  aexp_cases (induction a) Case; simpl;
    try reflexivity;
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity).
Qed.

Theorem fold_constants_bexp_sound :
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  bexp_cases (induction b) Case;
    try reflexivity.
  Case "BEq".
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1'.
    remember (fold_constants_aexp a2) as a2'.
    replace (aeval st a1) with (aeval st a1') by
        (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
        (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (beq_nat n n0); reflexivity.
  Case "BLe".
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1'.
    remember (fold_constants_aexp a2) as a2'.
    replace (aeval st a1) with (aeval st a1') by
        (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
        (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (ble_nat n n0); reflexivity.
  Case "BNot".
    simpl. remember (fold_constants_bexp b) as b'.
    rewrite IHb.
    destruct b'; reflexivity.
  Case "BAnd".
    simpl.
    remember (fold_constants_bexp b1) as b1'.
    remember (fold_constants_bexp b2) as b2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";". apply CSeq_congruence; assumption.
  Case "IFB".
    assert (bequiv b (fold_constants_bexp b)).
    SCase "Pf of assertion". apply fold_constants_bexp_sound.
    remember (fold_constants_bexp b) as b'.
    destruct b';
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
    assert (bequiv b (fold_constants_bexp b)).
    SCase "Pf of assertion". apply fold_constants_bexp_sound.
    remember (fold_constants_bexp b) as b'.
    destruct b';
      try (apply CWhile_congruence; assumption).
    SCase "b always true".
      apply WHILE_true. apply H.
    SCase "b always false".
      apply WHILE_false. apply H.
Qed.

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i' => if beq_id i i' then u else AId i'
  | APlus a1 a2 => APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 => AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 => AMult (subst_aexp i u a1) (subst_aexp i u a2)
end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53)) (APlus (AId Y) (AId X)) = (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity.
Qed.

Definition subst_equiv_property := forall i1 i2 a1 a2,
    cequiv (i1 ::= a1; i2 ::= a2)
           (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.
  remember (X ::= APlus (AId X) (ANum 1);
            Y ::= AId X)
           as c1.
  remember (X ::= APlus (AId X) (ANum 1);
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  remember (update (update empty_state X 1) Y 1) as st1.
  remember (update (update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state || st1);
  assert (H2: c2 / empty_state || st2);
  try (subst;
       apply E_Seq with (st' := (update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.
  assert (Hcontra: st1 = st2)
         by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
         by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.
Qed.

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  intros contra. unfold cequiv in contra.
  assert (H1: (forall st, SKIP / st || st)) by (apply E_Skip).
  assert (H2: SKIP / empty_state || empty_state) by (apply H1).
  apply contra in H2. apply WHILE_true_nonterm in H2. apply H2. apply refl_bequiv.
Qed.