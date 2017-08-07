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

Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem four_ev' :
  ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Definition four_ev : ev 4 := ev_SS 2 (ev_SS 0 ev_0).

Definition ev_plus4 : forall n, ev n -> ev (4+n) :=
  fun (n:nat) =>
    fun (e:ev n) =>
       ev_SS (2+n) (ev_SS n e).

Theorem ev_plus4' : forall n,
    ev n -> ev (4 + n).
Proof.
  intros. induction n as [| n'].
  (*Case "n = 0".*) simpl. apply four_ev.
  (*Case "n = S n'".*) simpl. apply ev_SS. apply ev_SS. apply H.
Qed.

Print ev_plus4'.

Theorem double_even : forall n,
    ev (double n).
Proof.
  intros. induction n as [| n'].
  (*Case "n = 0".*) simpl. apply ev_0.
  (*Case "n = S n'".*) simpl. apply ev_SS. apply IHn'.
Qed.

(*わかりませんですた*)
Print double_even.

Theorem ev_minus2 : forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'.
Qed.

Theorem ev_minus2_n : forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E. destruct n as [| n'].
  Case "n = 0". simpl. apply ev_0.
  Case "n = S n'". simpl. (*保留*)
Admitted.

Theorem ev_even : forall n,
    ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'.
Qed.

Theorem ev_even_n : forall n,
    ev n -> even n.
Proof.
  intros n E. induction n as [| n'].
  Case "n = 0".
    unfold even. reflexivity.
  Case "n = S n'".
    unfold even. (*保留*)
Admitted.

(*
Theorem l : forall n,
    ev n.
Proof.
  intros n. induction n.
  Case "O". simpl. apply ev_0.
  Case "S".
すべてのnについてev nは成り立たない
*)

Theorem ev_sum : forall n m,
    ev n -> ev m -> ev (n+m).
Proof.
  intros n m E F. induction E as [| n' E'].
  Case "E = ev_0". simpl. apply F.
  Case "E = ev_SS n' E'".
    simpl. apply ev_SS. apply IHE'.
Qed.

Theorem SSev_even : forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'.
Qed.

Theorem SSSSev_even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [| n' E'].
  inversion E' as [| n'' E'']. apply E''.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2+2=9.
Proof.
  intros. inversion H.
  inversion H1. inversion H3.
Qed.

Theorem ev_minus2' : forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'.
Qed.

Theorem ev_ev_even : forall n m,
    ev (n+m) -> ev n -> ev m.
Proof.
  intros n m E F. generalize dependent m.
  induction F as [| n' F'].
  Case "F = ev_0". intros. apply E.
  Case "F = ev_SS n' F'". intros.
    inversion E. apply IHF'. apply H0.
Qed.

Theorem ev_plus_plus : forall n m p,
    ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p E F.
(*わからん
恐らくev_ev_evenとev_sumを利用するのだとは思う
*)
Admitted.

Inductive MyProp : nat -> Prop :=
| MyProp1 : MyProp 4
| MyProp2 : forall n:nat, MyProp n -> MyProp (4 + n)
| MyProp3 : forall n:nat, MyProp (2 + n) -> MyProp n.

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3. simpl.
  assert (12 = 4 + 8) as H12.
    Case "Proof of assertion". reflexivity.
  rewrite -> H12.
  apply MyProp2.
  assert (8 = 4 + 4) as H8.
    Case "Proof of assertion". reflexivity.
  rewrite -> H8.
  apply MyProp2.
  apply MyProp1.
Qed.

Theorem MyProp_0 : MyProp 0.
Proof.
  apply MyProp3. apply MyProp3. simpl.
  apply MyProp1.
Qed.

Theorem MyProp_plustwo : forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  intros. apply MyProp3. simpl.
  apply MyProp2. apply H.
Qed.

Theorem MyProp_ev : forall n:nat,
    ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].
  Case "E = ev_0".
    apply MyProp_0.
  Case "E = ev_SS n' E'".
    apply MyProp_plustwo. apply IHE'.
Qed.

Theorem ev_MyProp : forall n:nat,
    MyProp n -> ev n.
Proof.
  intros n M. induction M.
  Case "M = MyProp1". apply ev_SS. apply ev_SS. apply ev_0.
  Case "M = MyProp2". apply ev_SS. apply ev_SS. apply IHM.
  Case "M = MyProp3". apply ev_sum with (m:=2) in IHM.
    rewrite -> plus_comm in IHM. simpl in IHM.
    inversion IHM. inversion H0. apply H2.
    apply ev_SS. apply ev_0.
Qed.

Theorem plus_comm' : forall n m : nat,
    n + m = m + n.
Proof.
  induction n as [| n'].
  Case "n = O". intros m. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'". intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem plus_comm'' : forall n m : nat,
    n + m = m + n.
Proof.
  induction m as [| m'].
  Case "m = O". simpl. rewrite -> plus_0_r. reflexivity.
  Case "m = S m'". simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.
Qed.

Check ev_ind.

(*
list_ind
  : forall (X : Type) (P : list X -> Prop),
    P [] ->
    forall (x : X) (l : list X), P l -> P (x :: l) ->
    forall l : list X, P l
*)

Check list_ind.

(*
MyProp_ind
  : forall P : nat -> Prop,
  P 4 ->
  (forall n : nat, MyProp n -> P n -> P (4 + n)) ->
  (forall n : nat, MyProp (2 + n) -> P (2 + n) -> P n) ->
  forall n : nat, MyProp n -> P n
*)

Check MyProp_ind.

Theorem ev_MyProp' : forall n:nat,
    MyProp n -> ev n.
Proof.
  apply MyProp_ind.
  Case "MyProp1". apply ev_SS. apply ev_SS. apply ev_0.
  Case "MyProp2". intros. apply ev_SS. apply ev_SS. apply H0.
  Case "MyProp3". intros. apply SSev_even in H0. apply H0.
Qed.

(*Definition MyProp_ev' : forall n:nat, ev n -> MyProp n :=*)

Module P.

Inductive p : (tree nat) -> nat -> Prop :=
  | c1 : forall n, p (leaf _ n) 1
  | c2 : forall t1 t2 n1 n2,
      p t1 n1 -> p t2 n2 -> p (node _ t1 t2) (n1 + n2)
  | c3 : forall t n, p t n -> p t (S n).

End P.

Inductive pal {X:Type} : list X -> Prop :=
| p_n : pal []
| p_c : forall v l, pal l -> pal (v :: (snoc l v))
| p_r : forall v l, v :: l = snoc (rev l) v -> pal (v :: l)
.
(*
１つ目と２つ目までは分かった３つ目がよくわからない
現状はコレだけど，l = rev l -> pal l と特に大差無いしダメだと思う
*)
  
Theorem rev_cons : forall (X:Type) (l:list X),
    pal (l ++ rev l).
Proof.
  intros. induction l as [| v l'].
  Case "l = []". simpl. apply p_n.
  Case "l = v :: l'".
    simpl. rewrite <- snoc_with_append.
    apply p_c. apply IHl'.
Qed.

Theorem pal_equal_rev : forall (X:Type) (l:list X),
    pal l -> l = rev l.
Proof.
  intros X l P. induction P.
  Case "p_n". simpl. reflexivity.
  Case "p_c". simpl. rewrite -> rev_snoc.
    simpl. rewrite <- IHP. reflexivity.
  Case "p_r".
    simpl. apply H.
Qed.

Theorem rev_pal : forall (X:Type) (l:list X),
    l = rev l -> pal l.
Proof.
  intros. induction l as [| v l'].
  Case "l = []". apply p_n.
  Case "l = v : l'". simpl in H.
    apply p_r. apply H.
Qed.

Inductive subseq : list nat -> list nat -> Prop :=
| s_1 : forall l, subseq l []
| s_2 : forall (n:nat) (l1 l2:list nat),
    subseq l1 l2 -> subseq (n :: l1) (n :: l2)
| s_3 : forall (n:nat) (l1 l2:list nat),
    subseq l1 l2 -> subseq (n :: l1) l2
. (*解けない->疲れた->保留する*)

Theorem subseq_relf : forall l,
    subseq l l.
Proof.
  intros. induction l as [| n l'].
  Case "l = []". apply s_1.
  Case "l = n :: l'". apply s_2. apply IHl'.
Qed.

(*元の練習問題ではfoo*)
Inductive foo'' (X : Set) (Y : Set) : Set :=
  | foo1 : X -> foo'' X Y
  | foo2 : Y -> foo'' X Y
  | foo3 : foo'' X Y -> foo'' X Y.
(*
foo_ind
     : forall (X Y : Set) (P : foo'' X Y -> Prop),
       (forall x : X, P (foo1 X Y x)) ->
       (forall y : Y, P (foo2 X Y y)) ->
       (forall f : foo'' X Y, P f -> P (foo3 X Y f)) ->
        forall f : foo'' X Y, P f
*)

Check foo''_ind.

(*
bar_ind
     : forall P : bar -> Prop,
       (forall n : nat, P (bar1 n)) ->
       (forall b : bar, P b -> P (bar2 b)) ->
       (forall (b : bool) (b0 : bar), P b0 -> P (bar3 b b0)) ->
       forall b : bar, P b
*)
(*元はbar*)
Inductive bar' : Set :=
| bar1 : nat -> bar'
| bar2 : bar' -> bar'
| bar3 : bool -> bar' -> bar'.

Check bar'_ind.

Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
| nlt_nil  : forall n, no_longer_than X [] n
| nlt_cons : forall x l n, no_longer_than X l n ->
                           no_longer_than X (x::l) (S n)
| nlt_succ : forall l n, no_longer_than X l n ->
                         no_longer_than X l (S n).

(*
no_longer_than_ind
     : forall (X : Set) (P : list X -> nat -> Prop),
       (forall n : nat, P [] n) ->
       (forall (x : X) (l : list X) (n : nat),
        no_longer_than X l n -> P l n ->
                                P (x::l) (S n)) ->
       (forall (l : list X) (n : nat),
        no_longer_than X l n -> P l n ->
                                P l (S n)) ->
       forall (l : list X) (n : nat), no_longer_than X l n ->
         P l n
*)

Check no_longer_than_ind.

Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n l, R n l -> R (S n) (n :: l)
  | c3 : forall n l, R (S n) l -> R n l.
(*
R 2 [1,0]     well-formed
R 1 [1,2,1,0] ill-formed
R 6 [3,2,1,0] ill-formed
*)