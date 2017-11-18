Require Export SfLib.


Module AExp.

Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (e:aexp) : nat :=
  match e with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (e:bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (e:aexp) : aexp :=
  match e with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 =>
    APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
    AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
    AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                 (APlus (ANum 0)
                 (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound : forall e,
    aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. induction e.
  Case "ANum". reflexivity.
  Case "APlus". destruct e1.
    SCase "e1 = ANum n". destruct n.
      SSCase "n = 0". simpl. apply IHe2.
      SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
    SCase "e1 = APlus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMinus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMult e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.
    Case "n=0". simpl. reflexivity.
    Case "n=Sn". simpl. reflexivity.
Qed.

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n;
    simpl;
    reflexivity.
Qed.

Theorem optimize_0plus_sound' : forall e,
    aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity).
  Case "ANum". reflexivity.
  Case "APlus".
    destruct e1;
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    SCase "e1 = ANum n".
      destruct n;
        simpl; rewrite IHe2; reflexivity.
Qed.

Theorem optimize_0plus_sound'' : forall e,
    aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    try reflexivity.
  Case "APlus".
    destruct e1; try (simpl; simpl in IHe1; rewrite IHe1;
                     rewrite IHe2; reflexivity).
    SCase "e1 = ANum n".
      destruct n; simpl; rewrite IHe2; reflexivity.
Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus" |
    Case_aux c "AMinus" | Case_aux c "AMult" ].

Theorem optimize_0plus_sound''' : forall e,
    aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  aexp_cases (induction e) Case;
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    try reflexivity.
  Case "APlus".
    aexp_cases (destruct e1) SCase;
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHe2; reflexivity.
Qed.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" |
    Case_aux c "BEq"   | Case_aux c "BLe" |
    Case_aux c "BNot"  | Case_aux c "BAnd" ].

Fixpoint optimize_0plus_b (e:bexp) : bexp :=
  match e with
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | _ => e
  end.

Example optimize_0plus_b_test1:
  optimize_0plus_b (BEq (APlus (ANum 0) (ANum 2))
                   (ANum 2))
  = (BEq (ANum 2) (ANum 2)).
Proof. reflexivity. Qed.

Theorem optimize_0plus_b_sound : forall e,
    beval (optimize_0plus_b e) = beval e.
Proof.
  intros e.
  bexp_cases (induction e) Case;
    try (simpl; rewrite optimize_0plus_sound;
         rewrite optimize_0plus_sound; reflexivity);
    try reflexivity.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n:nat),
    aevalR (ANum n) n
| E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (APlus e1 e2) (n1 + n2)
| E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMult e1 e2) (n1 * n2).

Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n:nat),
    (ANum n) || n
| E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
    (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
| E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
    (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
| E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
    (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)
where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum"   | Case_aux c "E_APlus" |
    Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

Theorem aeval_iff_aevalR : forall a n,
    (a || n) <-> aeval a = n.
Proof.
  split.
  Case "->".
    intros H.
    aevalR_cases (induction H) SCase; simpl.
    SCase "E_ANum".
      reflexivity.
    SCase "E_APlus".
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    SCase "E_AMinus".
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    SCase "E_AMult".
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
  Case "<-".
    generalize dependent n.
    aexp_cases (induction a) SCase;
      simpl; intros; subst.
    SCase "ANum".
      apply E_ANum.
    SCase "APlus".
      apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
    SCase "AMinus".
      apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
    SCase "AMult".
      apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
    (a || n) <-> aeval a = n.
Proof.
  split.
  Case "->".
    intros H; induction H; subst; reflexivity.
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
      try apply IHa1; try apply IHa2; reflexivity.
Qed.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive bevalR : bexp -> bool -> Prop :=
| E_BTrue :
    BTrue || true
| E_BFalse :
    BFalse || false
| E_BEq : forall (e1 e2 : aexp) (n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    (BEq e1 e2) || (beq_nat n1 n2)
| E_BLe : forall (e1 e2 : aexp) (n1 n2 : nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    (BLe e1 e2) || (ble_nat n1 n2)
| E_BNot : forall (e : bexp) (b : bool),
    e || b ->
    (BNot e) || (negb b)
| E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
    e1 || b1 ->
    e2 || b2 ->
    (BAnd e1 e2) || (andb b1 b2)
where "e '||' n" := (bevalR e n) : type_scope.

Tactic Notation "bevalR_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "E_BTrue" | Case_aux c "E_BFalse" |
   Case_aux c "E_BEq"   | Case_aux c "E_BLe" |
   Case_aux c "E_BNot"  | Case_aux c "E_BAnd" ].

Theorem beval_iff_bevalR : forall e b,
    (e || b) <-> beval e = b.
Proof.
  split.
  Case "->".
    intros H; induction H; simpl;
      try (apply aeval_iff_aevalR in H;
           apply aeval_iff_aevalR in H0);
      subst; reflexivity.
  Case "<-".
    generalize dependent b.
    induction e; simpl; intros; subst; constructor;
    try apply aeval_iff_aevalR;
    try apply IHe;
    try apply IHe1;
    try apply IHe2;
    reflexivity.
Qed.

End AExp.

Module Id.

Inductive id : Type :=
| Id : nat -> id.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall X,
    true = beq_id X X.
Proof.
  intros. destruct X.
  apply beq_nat_refl.
Qed.

Theorem beq_id_eq : forall i1 i2,
    true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros. destruct i1 as [n]. destruct i2 as [m].
  unfold beq_id in H. apply beq_nat_eq in H.
  subst. reflexivity.
Qed.

Theorem beq_id_false_not_eq : forall i1 i2,
    beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros. destruct i1 as [n]. destruct i2 as [m].
  unfold beq_id in H. apply beq_nat_false in H.
  (*ここからSfLiを見てしまいました*)
  intros C. apply H. inversion C. reflexivity.
Qed.

Theorem not_eq_beq_id_false : forall i1 i2,
    i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros. destruct i1 as [n]. destruct i2 as [m].
  (*ここからSfLibの中を見てしまいました*)
  assert (n <> m).
  Case "Proof of assertion".
    intros G. apply H. subst. reflexivity.
    apply not_eq_beq_false. apply H0.
Qed.

Theorem beq_id_sym : forall i1 i2,
    beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros. destruct i1 as [n]. destruct i2 as [m].
  unfold beq_id. apply beq_nat_sym.
Qed.

End Id.

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st:state) (X:id) (n:nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

Theorem update_eq : forall n X st,
    (update st X n) X = n.
Proof.
  intros. unfold update.
  rewrite <- beq_id_refl. reflexivity.
Qed.

Theorem update_neq : forall V2 V1 n st,
    beq_id V2 V1 = false ->
    (update st V2 n) V1 = (st V1).
Proof.
  intros. unfold update. rewrite H. reflexivity.
Qed.

Theorem update_example : forall (n:nat),
    (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros. unfold update. simpl. unfold empty_state. reflexivity.
Qed.

Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
    (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  intros. unfold update.
  destruct (beq_id k2 k1) as []eqn:?.
  (* 上の代わりに下記のtacticでもおｋ
  case_eq (beq_id k2 k1).
   *)
  Case "beq_id k2 k1 = true". reflexivity.
  Case "beq_id k2 k1 = false". reflexivity.
Qed.

Theorem update_same : forall x1 k1 k2 (f:state),
    f k1 = x1 ->
    (update f k1 x1) k2 = f k2.
Proof.
  intros. unfold update.
  destruct (beq_id k1 k2) as []eqn:?.
  Case "beq_id k1 k2 = true".
    apply eq_sym in Heqb.
    apply beq_id_eq in Heqb.
    rewrite <- H. rewrite Heqb. reflexivity.
  Case "beq_id k1 k2 = false".
    reflexivity.
Qed.

Theorem update_permute : forall x1 x2 k1 k2 k3 f,
    beq_id k2 k1 = false ->
    (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  intros. unfold update.
  case_eq (beq_id k1 k3); intros.
  Case "beq_id k1 k3 = true".
    apply eq_sym in H0. apply beq_id_eq in H0.
    subst. rewrite H. reflexivity.
  Case "beq_id k1 k3 = false".
    reflexivity.
Qed.

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : id -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.


Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity.
Qed.

Example bexp1 :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity.
Qed.

Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
        Y ::= AMult (AId Y) (AId Z);
        Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1);
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3;
  Z ::= ANum 5;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
        SKIP
  END.

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z) ;
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X ;
  Y ::= ANum 1 ;
  fact_loop.

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
  | SKIP =>
    st
  | l ::= a1 =>
          update st l (aeval st a1)
  | c1 ; c2 =>
    let st' := ceval_step1 st c1 in 
    ceval_step1 st' c2
  | IFB b THEN c1 ELSE c2 FI =>
    if (beval st b)
         then ceval_step1 st c1
         else ceval_step1 st c2
  | WHILE b1 DO c1 END =>
    st
end.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O  => empty_state
  | S i' =>
    match c with
    | SKIP =>
      st
    | l ::= a1 =>
            update st l (aeval st a1)
    | c1 ; c2 =>
      let st' := ceval_step2 st c1 i' in 
      ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b)
      then ceval_step2 st c1 i'
      else ceval_step2 st c2 i'
    | WHILE b1 DO c1 END =>
      if (beval st b1)
      then let st' := ceval_step2 st c1 i' in
           ceval_step2 st' c i'
      else st
    end
end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
    | SKIP =>
      Some st
    | l ::= a1 =>
            Some (update st l (aeval st a1))
    | c1 ; c2 =>
      match (ceval_step3 st c1 i') with
      | Some st' => ceval_step3 st' c2 i'
      | None => None
      end
    | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b)
      then ceval_step3 st c1 i'
      else ceval_step3 st c2 i'
    | WHILE b1 DO c1 END =>
      if (beval st b1)
      then match (ceval_step3 st c1 i') with
           | Some st' => ceval_step3 st' c i'
           | None => None
           end
      else Some st
    end
end.

Notation "'LETOPT' x <== e1 'IN' e2" :=
  (match e1 with
   | Some x => e2
   | None => None
   end)
    (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
    | SKIP =>
      Some st
    | l ::= a1 =>
            Some (update st l (aeval st a1))
    | c1 ; c2 =>
      LETOPT st' <== ceval_step st c1 i' IN
             ceval_step st' c2 i'
    | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b)
      then ceval_step st c1 i'
      else ceval_step st c2 i'
    | WHILE b1 DO c1 END =>
      if (beval st b1)
      then LETOPT st' <== ceval_step st c1 i' IN
                  ceval_step st' c i'
      else Some st
    end
end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Definition pup_to_n : com :=
  Y ::= ANum 0;
  WHILE (BLe (ANum 1) (AId X)) DO
        Y ::= APlus (AId Y) (AId X);
        X ::= AMinus (AId X) (ANum 1)
  END.

Example pup_to_n_1 :
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st || (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st || st' ->
      c2 / st' || st'' ->
      (c1; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st''
where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse" | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Example ceval_example1:
  (X ::= ANum 2;
  IFB BLe (AId X) (ANum 1) THEN
    Y ::= ANum 3
  ELSE
    Z ::= ANum 4
  FI)
    / empty_state
    || (update (update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.

Example ceval_example2:
  (X ::= ANum 0; Y ::= ANum 1; Z ::= ANum 2) / empty_state ||
  (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (update empty_state X 0).
  apply E_Ass. reflexivity.
  apply E_Seq with (update (update empty_state X 0) Y 1).
  apply E_Ass. reflexivity.
  apply E_Ass. reflexivity.
Qed.

Theorem ceval_step__ceval : forall c st st',
    (exists i, ceval_step st c i = Some st') ->
    c / st || st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i'].
  Case "i = 0 -- contradictory".
    intros c st st' H. inversion H.
  Case "i = S i'".
    intros c st st' H.
    com_cases (destruct c) SCase;
      simpl in H; inversion H; subst; clear H.
    SCase "SKIP". apply E_Skip.
    SCase "::=". apply E_Ass. reflexivity.
    SCase ";".
      remember (ceval_step st c1 i') as r1. destruct r1.
      SSCase "Evaluation of r1 terminates normally".
        apply E_Seq with s.
          apply IHi'. rewrite Heqr1. reflexivity.
          apply IHi'. simpl in H1. assumption.
      SSCase "Otherwise -- contradiction".
        inversion H1.
    SCase "IFB".
      remember (beval st b) as r. destruct r.
      SSCase "r = true".
        apply E_IfTrue. rewrite Heqr. reflexivity.
        apply IHi'. assumption.
      SSCase "r = false".
        apply E_IfFalse. rewrite Heqr. reflexivity.
        apply IHi'. assumption.
    SCase "WHILE". remember (beval st b) as r. destruct r.
      SSCase "r = true".
        remember (ceval_step st c i') as r1. destruct r1.
        SSSCase "r1 = Some s".
          apply E_WhileLoop with s. rewrite Heqr. reflexivity.
          apply IHi'. rewrite Heqr1. reflexivity.
          apply IHi'. simpl in H1. assumption.
        SSSCase "r1 = None".
          inversion H1.
      SSCase "r = false".
        inversion H1.
        apply E_WhileEnd.
        rewrite Heqr. subst. reflexivity.
Qed.

Theorem ceval_step_more : forall i1 i2 st st' c,
    i1 <= i2 ->
    ceval_step st c i1 = Some st' ->
    ceval_step st c i2 = Some st'.
Proof.
  induction i1 as [| i1']; intros i2 st st' c Hle Hceval.
  Case "i1 = 0".
    inversion Hceval.
  Case "i1 = S i1'".
    destruct i2 as [| i2']. inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    com_cases (destruct c) SCase.
    SCase "SKIP".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase "::=".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase ";".
      simpl in Hceval. simpl.
      remember (ceval_step st c1 i1') as st1'o.
      destruct st1'o.
      SSCase "st1'o = Some".
        symmetry in Heqst1'o.
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "st1'o = None".
        inversion Hceval.
    SCase "IFB".
      simpl in Hceval. simpl.
      remember (beval st b) as bval.
      destruct bval; apply (IHi1' i2') in Hceval; assumption.
    SCase "WHILE".
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      remember (ceval_step st c i1') as st1'o.
      destruct st1'o.
      SSCase "st1'o = Some".
        symmetry in Heqst1'o.
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "st1'o = None".
        simpl in Hceval. inversion Hceval.
Qed.

Theorem ceval__ceval_step : forall c st st',
    c / st || st' ->
    exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  ceval_cases (induction Hce) Case.
  Case "E_Skip". exists 1. reflexivity.
  Case "E_Ass". exists 1. simpl. rewrite H. reflexivity.
  Case "E_Seq". destruct IHHce1. destruct IHHce2.
    exists (1 + x + x0). simpl.
    remember (ceval_step st c1 (x + x0)) as r.
    destruct r.
    SCase "r = Some".
      apply ceval_step_more with (i2 := (x + x0)) in H.
      rewrite H in Heqr. inversion Heqr.
      apply ceval_step_more with (i1 := x0). omega.
      assumption. omega.
    SCase "r = None".
      apply ceval_step_more with (i2 := (x + x0)) in H.
      rewrite H in Heqr. inversion Heqr. omega.
  Case "E_IfTrue". destruct IHHce.
    exists (1 + x). simpl. rewrite H. apply H0.
  Case "E_IfFalse". destruct IHHce.
    exists (1 + x). simpl. rewrite H. apply H0.
  Case "E_WhileEnd". exists 1. simpl. rewrite H. reflexivity.
  Case "E_WhileLoop". destruct IHHce1. destruct IHHce2.
    exists (1 + x + x0). simpl. rewrite H.
    remember (ceval_step st c1 (x + x0)) as r.
    destruct r.
    SCase "r = Some".
      apply ceval_step_more with (i2 := x + x0) in H0.
      rewrite H0 in Heqr. inversion Heqr.
      apply ceval_step_more with (i2 := x + x0) in H1.
      assumption. omega. omega.
    SCase "r = None".
      apply ceval_step_more with (i2 := x + x0) in H0.
      rewrite H0 in Heqr. inversion Heqr. omega.
Qed.

Theorem ceval_and_ceval_step_coincide : forall c st st',
    c / st || st'
    <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

Theorem ceval_deterministic : forall c st st1 st2,
    c / st || st1 ->
    c / st || st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
    intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
    SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to true".
      reflexivity.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to false".
      assert (st' = st'0) as EQ1.
      SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.
Qed.

Theorem ceval_deterministic' : forall c st st1 st2,
    c / st || st1 ->
    c / st || st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega.
Qed.

Theorem plus2_spec : forall st n st',
    st X = n ->
    plus2 / st || st' ->
    st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst.
  apply update_eq.
Qed.

Theorem XtimesYinZ_spec : forall st st' n m,
    st X = n ->
    st Y = m ->
    XtimesYinZ / st || st' ->
    st' Z = n * m.
Proof.
  intros st st' n m HX HY Heval.
  inversion Heval. subst.
  apply update_eq.
Qed.

Theorem loop_never_stops : forall st st',
    ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  induction contra; inversion Heqloopdef.
    Case "E_WhileEnd".
      rewrite H1 in H. simpl in H. inversion H.
    Case "E_WhileLoop". contradiction.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1 ; c2 => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END => false
  end.

(*
Inductive no_whilesR: com -> Prop :=
| NW_Skip : no_whilesR SKIP
| NW_Ass : forall l a,
    no_whilesR (l ::= a)
| NW_Seq : forall c1 c2,
    no_whilesR c1 ->
    no_whilesR c2 ->
    no_whilesR (c1 ; c2)
| NW_If : forall c1 c2 b,
    no_whilesR c1 ->
    no_whilesR c2 ->
    no_whilesR (IFB b THEN c1 ELSE c2 FI)
.

Theorem no_whiles_eqv : forall c,
    no_whiles c = true <-> no_whilesR c.
Proof.
  intros. split.
  Case "->". intro.
    com_cases (induction c) SCase; try (constructor).
    SCase ";".
      simpl in H. apply IHc1. rewrite <- H.
*)