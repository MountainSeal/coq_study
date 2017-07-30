Require Export Poly.
Require Export Basics.

Check (2 + 2 = 4).

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true : plus_fact.
Proof. reflexivity. Qed.

Definition strange_prop1 : Prop :=
  (2 + 2 = 5) -> (99 + 26 = 42).
Definition strange_prop2 : Prop :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 =true).

Definition even (n:nat) : Prop :=
  evenb n = true.

Check even.
Check (even 4).
Check (even 3).

Definition even_n__even_SSn (n:nat) : Prop :=
  (even n) -> (even (S (S n))).

Definition between (n m o:nat) : Prop :=
  and (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat->Prop := between 13 19.

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

Definition true_for_n__true_for_Sn (P:nat->Prop) (n:nat) : Prop :=
  P n -> P (S n).

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P:nat->Prop) : Prop :=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).

Inductive good_day : day -> Prop :=
| gd_sat : good_day saturday
| gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

Inductive day_before : day -> day -> Prop :=
| db_tue : day_before tuesday monday
| db_wed : day_before wednesday tuesday
| db_thu : day_before thursday wednesday
| db_fri : day_before friday thursday
| db_sat : day_before saturday friday
| db_sun : day_before sunday saturday
| db_mon : day_before monday sunday.

Inductive fine_day_for_singing : day -> Prop :=
| fdfs_any : forall d:day, fine_day_for_singing d.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.

Check fdfs_wed.
Check fdfs_wed'.

Inductive ok_day : day -> Prop :=
| okd_gd : forall d,
    good_day d ->
    ok_day d
| okd_before : forall d1 d2,
    ok_day d2 ->
    day_before d2 d1 ->
    ok_day d1.

Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
             (okd_before thursday friday
                         (okd_before friday saturday
                                     (okd_gd saturday gd_sat)
                                     db_sat)
                         db_fri)
             db_thu.

Theorem okdw' : ok_day wednesday.
Proof.
  apply okd_before with (d2:=thursday).
  apply okd_before with (d2:=friday).
  apply okd_before with (d2:=saturday).
  apply okd_gd. apply gd_sat.
  apply db_sat. apply db_fri.
  apply db_thu.
Qed.

Print okdw'.

Definition okd_before2 := forall d1 d2 d3,
    ok_day d3 ->
    day_before d2 d1 ->
    day_before d3 d2 ->
    ok_day d1.

Theorem okd_before2_valid : okd_before2.
Proof.
  unfold okd_before2. intros d1 d2 d3 H1 H2 H3.
  apply okd_before with d2.
  apply okd_before with d3.
  apply H1. apply H3. apply H2.
Qed.

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) =>
  fun (H : ok_day d3) =>
  fun (H0 : day_before d2 d1) =>
  fun (H1 : day_before d3 d2) =>
  okd_before d1 d2 (okd_before d2 d3 H H1) H0.

Print okd_before2_valid.

Check nat_ind.

Theorem mult_0_r' : forall n:nat,
    n * 0 = 0.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn.
    reflexivity.
Qed.

Theorem plus_one_r' : forall n:nat,
    n + 1 = S n.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn.
    reflexivity.
Qed.

Inductive yesno : Type :=
| yes : yesno
| no : yesno.

Check yesno_ind.

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.

Check rgb_ind.

Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
| nnil1 : natlist1
| nsnoc1 : natlist1 -> nat -> natlist1.

Inductive ExSet : Type :=
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive tree (X:Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.

Check tree_ind.

Inductive mytype (X:Type) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y:Type) : Type :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Inductive foo' (X:Type) : Type :=
| C1 : list X -> foo' X -> foo' X
| C2 : foo' X.

(*
foo'_ind :
  forall (X:Type) (P: foo' X -> Prop),
    (forall (l : list X) (f : foo' X),
      P f ->
      P (C1 X l f) ->
    P (C2 X) ->
    forall f : foo' X, P f

*)

