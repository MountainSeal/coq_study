Require Export "Prop".
Require Export "Basics".

Definition funny_prop1 := forall n, forall (E : ev n), ev (n+4).

Definition funny_prop1' := forall n, forall (_ : ev n), ev (n+4).

Definition funny_prop1'' := forall n, ev n -> ev (n+4).

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example :
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  apply ev_0.
  apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Print and_example.

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
  Case "left". apply ev_0.
  Case "right". apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP.
Qed.

Theorem proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
  apply HQ.
  apply HP.
Qed.

Print and_commut.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split. split.
  apply HP. apply HQ. apply HR.
Qed.

Theorem even_ev : forall n : nat,
    (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". split.
  SCase "left". intro H. apply ev_0.
  SCase "right". intro H. inversion H.
  Case "n = S n'". inversion IHn' as [LIHn' RIHn']. split.
    SCase "left". apply RIHn'.
    SCase "right". intros H.
    apply ev_SS. apply LIHn'.
    inversion H. unfold even. apply H1.
Qed.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R:Prop) (H1: P /\ Q) (H2: Q /\ R) =>
      match H1 with
      | conj HP HQ1 =>
        match H2 with
        | conj HQ2 HR =>
          (conj P R) HP HR
        end
      end.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                        (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
    (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB.
Qed.

Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.
Qed.

Theorem iff_refl : forall P : Prop,
    P <-> P.
Proof.
  intros H. split.
  Case "->". intro H1. apply H1.
  Case "<-". intro H2. apply H2.
Qed.

Theorem iff_trans : forall P Q R : Prop,
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2.
  inversion H1 as [H1_1 H1_2].
  inversion H2 as [H2_1 H2_2].
  split.
  Case "->". intro H3. apply H2_1. apply H1_1. apply H3.
  Case "<-". intro H3. apply H1_2. apply H2_2. apply H3.
Qed.

Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  fun (n:nat) => conj (MyProp n -> ev n) (ev n -> MyProp n) (ev_MyProp n) (MyProp_ev n)
.

Theorem MyProp_iff_ev' : forall n,
    MyProp n <-> ev n.
Proof.
  intros. split. apply ev_MyProp. apply MyProp_ev.
Qed.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.

Check or_intror.

Theorem or_commut : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  (*Case "right".*) apply or_intror. apply HP.
  (*Case "left".*) apply or_introl. apply HQ.
Qed.

Theorem or_commut' : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  Case "right". right. apply HP.
  Case "left". left. apply HQ.
Qed.

Print or_commut.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
    P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
  Case "left". split.
    SCase "left". left. apply HP.
    SCase "right". left. apply HP.
  Case "right". split.
    SCase "left". right. apply HQ.
    SCase "right". right. apply HR.
Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
    (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H. inversion H as [H1 H2].
  inversion H1 as [HP | HQ].
  Case "left". left. apply HP.
  Case "right". inversion H2 as [HP' | HR].
    SCase "left". left. apply HP'.
    SCase "right". right. split.
      SSCase "left". apply HQ.
      SSCase "right". apply HR.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  Case "->". apply or_distributes_over_and_1.
  Case "<-". apply or_distributes_over_and_2.
Qed.

Theorem andb_true_and : forall b c,
    andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". destruct c.
    SCase "c = true". apply conj. reflexivity. reflexivity.
    SCase "c = false". inversion H.
  Case "b = false". inversion H.
Qed.

Theorem and_andb_true : forall b c,
    b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity.
Qed.

Theorem andb_false : forall b c,
    andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H. destruct b.
  Case "b = true". destruct c.
    SCase "c = true". inversion H.
    SCase "c = false". right. reflexivity.
  Case "b = false". destruct c.
    SCase "c = true". left. reflexivity.
    SCase "c = false". left. reflexivity.
Qed.

Theorem orb_true : forall b c,
    orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H. destruct b.
  Case "b = true". left. reflexivity.
  Case "b = false". right. destruct c.
    SCase "c = true". reflexivity.
    SCase "c = false". inversion H.
Qed.

Theorem orb_false : forall b c,
    orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H. destruct b.
  Case "b = true". destruct c.
    SCase "c = true". inversion H.
    SCase "c = false". inversion H.
  Case "b = true". destruct c.
    SCase "c = true". inversion H.
    SCase "c = false". split. reflexivity. reflexivity.
Qed.

Inductive False : Prop := .

Theorem False_implies_nonsense : False -> 2 + 2 = 5.
Proof.
  intros contra. inversion contra.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
    False -> P.
intros P contra. inversion contra.
Qed.

Inductive True : Prop := (*ﾔﾊﾞ...ﾜｶﾝﾅｲﾈ...*).

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~ ~ P.
Proof.
    intros P H. unfold not. intros G. apply G. apply H.
Qed.

(*言葉の使い方が間違っていましたら申し訳ありません
定理：
任意の命題Pについて，「Pならば~~P」が成り立つ．
証明：
~~Pを展開すると，(P -> False) -> Falseとなる．
(P -> False)をGとおく．
GよりPが導出され，Hより命題Pは成り立つ．
よって成り立つ．
*)

Theorem contrapositive : forall P Q : Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. unfold not. intros CP.
  intro HP. apply CP. apply H. apply HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
    ~ (P /\ ~P).
Proof.
  unfold not. intros P H. inversion H as [HP CP].
  apply CP. apply HP.
Qed.

Theorem five_not_even : ~ ev 5.
Proof.
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.
Qed.

Theorem ev_not_ev_S : forall n,
    ev n -> ~ ev (S n).
Proof.
  unfold not. intros n H. induction H.
  Case "ev_0". intros Hev1. inversion Hev1.
  Case "ev_SS". intros HevSSS. apply IHev.
    inversion HevSSS. apply H1.
Qed.

Theorem classic_double_neg : forall P : Prop,
    ~~P -> P.
Proof.
  intros P H. unfold not in H.
Admitted.

Definition peirce := forall P Q : Prop,
    ((P -> Q) -> P) -> P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Theorem test1 : forall P : Prop,
    P -> (P \/ ~P).
Proof.
  intros. left. apply H.
Qed.

Theorem classic_iff_exluded_middle :
  classic <-> excluded_middle.
Proof.
  unfold classic. unfold excluded_middle. split.
  Case "->". intros. apply H. unfold not.
    intros HO. apply HO. right. intro HP.
    apply H. unfold not. intros F. apply HO.
    left. apply HP.
  Case "<-". intros. unfold not in H0.
    apply ex_falso_quodlibet.
    apply H0. intro HP.
    apply test1 in HP. inversion HP.
    SCase "left". admit.
    SCase "right". apply H0. apply H1.
(*うーん，無理*)
Admitted.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
    b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
Qed.

Theorem not_eq_beq_false : forall n n' : nat,
    n <> n' -> beq_nat n n' = false.
Proof.
  intros n n' H. unfold not in H.
(*お手上げ*)
Admitted.

Inductive ex (X:Type) (P : X -> Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Definition some_nat_is_even : Prop :=
  ex nat ev.

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Notation "'exists' x , p" := (ex _ (fun x => p))
                               (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X, p" := (ex _ (fun x => p))
                                  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity.
Qed.

Example exists_example_1' : exists n,
    n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) ->
    (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(*ある自然数nが存在して，nの次の数が偶数である．*)
Definition p : ex nat (fun n => ev (S n)) :=
  (*マテマティカ*)
admit.

Theorem p_t : exists n,
    ev (S n).
Proof.
  exists 1.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem dist_not_exists : forall (X:Type) (P:X->Prop),
    (forall x, P x) -> ~(exists x, ~P x).
Proof.
  intros X P H. unfold not.
  intros G. inversion G as [w wH].
  apply wH. apply H.
Qed.

(*not_exists_distは飛ばした*)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  Case "->". intros H.
    inversion H as [x G]. inversion G as [GP | GQ].
    SCase "left". left. exists x. apply GP.
    SCase "right". right. exists x. apply GQ.
  Case "<-". intros H.
    inversion H as [HP | HQ].
    SCase "left". inversion HP as [x G].
      exists x. left. apply G.
    SCase "right". inversion HQ as [x G].
      exists x. right. apply G.
Qed.

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.

Notation "x = y" := (eq _ x y)
                      (at level 70, no associativity) : type_scope.

Inductive eq' (X:Type) (x:X) : X -> Prop :=
  refl_equal' : eq' X x x.

Notation "x =' y" := (eq' _ x y)
                       (at level 70, no associativity) : type_scope.

Theorem two_defs_of_eq_coincide : forall (X:Type) (x y:X),
    x = y <-> x =' y.
Proof.
  intros X x y. split.
  Case "->". intros H.
    inversion H. apply refl_equal'.
  Case "<-". intros H.
    inversion H. apply refl_equal.
Qed.

Check eq'_ind.

Definition four : 2 + 2 = 1 + 3 :=
  refl_equal nat 4.
Definition singleton : forall (X:Set) (x:X),
    []++[x] = x::[] :=
  fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEquality.

Module LeFirstTry.

Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall n m, (le n m) -> (le n (S m)).

Check le_ind.

End LeFirstTry.

Inductive le (n:nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n.
Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.
  intros H. inversion H. inversion H1.
Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
| nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
| ne_1 : ev (S n) -> next_even n (S n)
| ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation (a b:nat) (r : nat -> nat -> Prop) : Prop :=
| tot : (r a b) \/ (r b a) -> total_relation a b r.

Inductive empty_relation (n m:nat) : Prop -> Prop :=
| emp : empty_relation n m ((le n m) /\ (le m n)).

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
| c1 : R 0 0 0
| c2 : forall m n o, R m n o -> R (S m) n (S o)
| c3 : forall m n o, R m n o -> R m (S n) (S o)
| c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
| c5 : forall m n o, R m n o -> R n m o.
(*R_provability*)
(*1:この関係Rの定義からコンストラクタc5を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？
１つ目と２つ目の自然数が等しい場合に限定されるようになる
*)
(*2:この関係Rの定義からコンストラクタc4を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？
３つ目の自然数が偶数の場合に限定されるようになる
*)

End R.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| al_nil : all X P []
| al_cons : forall (x:X) (l:list X), P x -> all X P l -> all X P (x::l).

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem andb_true_l : forall b c:bool,
    andb b c = true -> b = true.
Proof.
  intros. destruct b.
  reflexivity.
  inversion H.
Qed.

Theorem andb_true_r : forall b c:bool,
    andb b c = true -> c = true.
Proof.
  intros. destruct b.
  simpl in H. apply H.
  inversion H.
Qed.

Theorem all_forallb : forall (X:Type) (test:X->bool) (l:list X),
    forallb test l = true <-> all X (fun x => test x = true) l.
Proof.
  intros. split.
  Case "->". intros. induction l as [| n l'].
    SCase "l = []". apply al_nil.
    SCase "l = n::l'". apply al_cons.
      apply andb_true_l in H. apply H.
      apply IHl'. apply andb_true_r in H. apply H.
  Case "<-". intros. induction l as [| n l'].
    SCase "l = []". reflexivity.
    SCase "l = n::l'". inversion H. simpl.
      rewrite H2. rewrite IHl'. reflexivity.
      apply H3.
Qed.