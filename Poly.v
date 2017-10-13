Require Export Lists.
Require Export Basics.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length X t)
end.

Example test_length1 :
  length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
  length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons X h (app X t l2)
end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil => nil X
  | cons h t =>snoc X (rev X t) h
end.

Example test_rev1 :
  rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2 :
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons X h (app' X t l2)
end.

Check app'.
Check app.

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length' _ t)
end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil nat))).

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(* 暗黙の引数*)
Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length'' t)
end.

Definition mynil : list nat := nil.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
         (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Definition list123''' := [1,2,3].

Fixpoint repeat (X:Type) (n : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' => cons n (repeat X n count')
end.

Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X,
      app [] l = l.
Proof. simpl. reflexivity. Qed.

Theorem rev_snoc : forall X : Type,
    forall v : X,
    forall s : list X,
      rev (snoc s v) = v :: (rev s).
Proof.
  intros. induction s as [| v' s'].
  Case "s = nil".
    simpl. reflexivity.
  Case "s = v' :: s'".
    simpl. rewrite -> IHs'. simpl. reflexivity.
Qed.

Theorem snoc_with_append :
  forall X : Type,
  forall l1 l2 : list X,
  forall v : X,
    snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros. induction l1 as [| v' l1'].
  Case "l1 = nil".
    simpl. reflexivity.
  Case "l1 = v' l1'".
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X][Y]].

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y: Type} (p : X*Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y: Type} (p : X*Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
end.

Fixpoint combine' {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [],_ => []
  | _,[] => []
  | x::tx, y::ty => (x,y) :: (combine' tx ty)
end.

Check @combine.

Eval simpl in (combine [1,2] [false, false, true, true]).

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | h :: t =>
    match h with
    | (x,y) =>
      (x :: fst (split t), y :: snd (split t))
    end
  end
.

Example test_split: split [(1,false), (2,false)] = ([1,2],[false,false]).
Proof. reflexivity. Qed.

Inductive option (X : Type) : Type :=
| some : X -> option X
| none : option X.

Implicit Arguments some [[X]].
Implicit Arguments none [[X]].

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
  | [] => none
  | a :: l' => if beq_nat n O then some a else index (pred n) l'
end.
Example test_index1 : index 0 [4,5,6,7] = some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1],[2]] = some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = none.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X :=
  match l with
  | [] => none
  | h :: _ => some h
end.

Check @hd_opt.

Example test_hd_opt1 : hd_opt [1,2] = some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1],[2]] = some [1].
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3: plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3': doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'': doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
           (f : X * Y -> Z) (x:X) (y:Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
           (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with (x,y) => (f x) y end.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof. intros. compute. reflexivity. Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof. intros. destruct p. compute. reflexivity. Qed.

Fixpoint filter {X:Type} (test : X -> bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t) else filter test t
end.

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X:Type} (l: list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2: filter length_is_1 [[1,2], [3], [4], [5,6,7], [], [8]] = [[3], [4], [8]].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun': doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (fun l => beq_nat (length l) 1)
         [[1,2], [3], [4], [5,6,7], [], [8]] = [[3], [4], [8]].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l:list nat) : list nat :=
  filter (fun n => andb (evenb n) (blt_nat 7 n)) l.


Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.

Definition partition {X:Type} (test : X -> bool) (l : list X) : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Fixpoint partition' {X:Type} (test : X -> bool) (l : list X) : list X * list X :=
  match l with
  | [] => ([], [])
  | h :: t => let tmp := partition' test t
              in if test h
              then (h :: (fst tmp), snd tmp)
              else (fst tmp, h :: (snd tmp))
end.

Example test_partition1: partition' oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.
Example test_partition2: partition' (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
end.

Example test_map1 : map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.

Example test_map2 : map oddb [2,1,2,5] = [false, true, false, true].
Proof. reflexivity. Qed.

Example test_map3 :
  map (fun n => [evenb n, oddb n]) [2,1,2,5] = [[true,false], [false,true], [true,false], [false,true]].
Proof. reflexivity. Qed.

Theorem map_snoc : forall (X Y : Type) (f : X -> Y) (l : list X) (x : X),
    map f (snoc l x) = snoc (map f l) (f x). 
Proof.
  intros. induction l as [| x' l']. 
  Case "l = nil".
    simpl. reflexivity.
  Case "l = x' :: l'".
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros. induction l as [| x l'].
  Case "l = nil".
    simpl. reflexivity.
  Case "l = x :: l'".
    simpl. rewrite -> map_snoc. rewrite -> IHl'. reflexivity.
Qed.

Fixpoint flat {X:Type} (ll:list (list X)): list X :=
  match ll with
  | [] => []
  | l :: tl =>
    match l with
    | [] => flat tl
    | _  => l ++ flat tl
    end
  end
.

Example test_flat1:
  flat [[1,1,1],[5,5,5],[4,4,4]]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.
Example test_flat2:
  flat [[1], [], [2,3], [4,5]]
  = [1,2,3,4,5].
Proof. reflexivity. Qed.

Fixpoint flat_map {X Y:Type} (f: X -> list Y) (l:list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) ++ flat_map f t
end.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X): option Y :=
  match xo with
  | none => none
  | some x => some (f x)
end.

(*以下のfilter'およびmap'は練習問題の解答*)
Fixpoint filter' (X:Type) (test : X -> bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter' X test t) else filter' X test t
end.

Fixpoint map' (X Y:Type) (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map' X Y f t)
end.

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1: fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example2: fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.
Example fold_example3: fold app [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

Definition constfun {X:Type} (x:X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1: ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2: (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X:Type} (f:nat->X) (k:nat) (x:X) : nat->X :=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.
Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.
Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.
Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example : forall (b:bool),
    (override (constfun b) 3 true) 2 = b.
Proof.
  intro. destruct b.
  Case "b = true". reflexivity.
  Case "b = false". reflexivity.
Qed.

Theorem unfold_example_bad : forall m n,
    3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros m n H. (*Admitted.*)
  rewrite <- H. simpl. reflexivity.
Qed.

Theorem unfold_example : forall m n,
    3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.
Qed.

Theorem override_eq : forall {X:Type} x k (f:nat->X),
    (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f:nat->X),
    f k1 = x1 -> beq_nat k2 k1 = false -> (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H I.
  unfold override.
  rewrite -> I. rewrite -> H.
  reflexivity.
Qed.

Theorem eq_add_s : forall (n m : nat),
    S n = S m -> n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.
Qed.

Theorem silly4 : forall (n m : nat),
    [n] = [m] -> n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.
Qed.

Theorem silly5 : forall (n m o : nat),
    [n,m] = [o,o] -> [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity.
Qed.

Example sillyex1: forall (X:Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
  intros X x y z l j H G.
  inversion H. inversion G. rewrite -> H1. reflexivity.
Qed.

Theorem silly6 : forall (n : nat),
    S n = 0 -> 2 + 2 = 5.
Proof.
  intros n H. inversion H.
Qed.

Theorem silly7 : forall (n m : nat),
    false = true -> [n] = [m].
Proof.
  intros n m contra. inversion contra.
Qed.

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1. 
Qed.

Lemma eq_remove_S : forall n m,
    n = m -> S n = S m.
Proof.  intros n m eq. rewrite -> eq. reflexivity. Qed.

Theorem beq_nat_eq : forall n m,
    true = beq_nat n m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    intros m. destruct m as [| n'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. intros contra. inversion contra.
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m'". simpl. intros H.
      apply eq_remove_S. apply IHn'. apply H.
Qed.

Theorem beq_nat_eq' : forall m n,
    beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m'].
  Case "m = 0".
    intros n. induction n as [| n'].
    SCase "n = 0". simpl. reflexivity.
    SCase "n = S n'". simpl. intros contra. inversion contra.
  Case "m = S m'".
    intros n. induction n as [| n'].
    SCase "n = 0". simpl. intros contra. inversion contra.
    SCase "n = S n'". simpl.
      intros H. apply eq_remove_S. apply IHm'. apply H.
Qed.

Theorem length_snoc' : forall (X:Type) (v:X)
                              (l:list X) (n:nat),
    length l = n -> length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [|v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl.
    destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply eq_remove_S. apply IHl'. inversion eq. reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
    true = beq_nat 0 n -> 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = S n'". simpl. intros contra. inversion contra.
Qed.

Theorem beq_nat_0_r : forall n,
    true = beq_nat n 0 -> 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = S n'".
    simpl. intros contra. inversion contra.
Qed.

Theorem double_injective : forall n m,
    double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". simpl. intros m eq. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'". intros m eq. destruct m as [| m'].
    SCase "m = 0". inversion eq.
    SCase "m = S m'".
      apply eq_remove_S. apply IHn'. inversion eq. reflexivity.
Qed.

Theorem S_inj : forall (n m : nat) (b: bool),
    beq_nat (S n) (S m) = b ->
    beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H.
Qed.

Theorem silly3' : forall (n : nat),
    (beq_nat n 5 = true ->
    beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m ->
    n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". intro H. inversion H.
  Case "n = S n'".
    destruct m as [| m'].
    SCase "m = 0". intro H. inversion H.
    SCase "m = S m'".
      intro H. (*この段階でdouble_plusとdouble_injectiveを使えばとけそう*)
      simpl in H.
      rewrite -> plus_comm in H. simpl in H. rewrite <- double_plus in H.
      rewrite -> plus_comm in H. simpl in H. rewrite <- double_plus in H.
      inversion H. apply double_injective in H1.
      rewrite -> H1. reflexivity.
Qed. (*ヌワンツ・カレタモ*)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false : forall (n : nat),
    sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.
Qed.

Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f:nat->X),
    (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f. unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true". reflexivity.
  Case "beq_nat k1 k2 = false". reflexivity.
Qed.

(*combine_splitとsplit_combineは後でゆっくりやる*)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  destruct e3.
  Case "e3 = true". apply beq_nat_eq in Heqe3.
    rewrite -> Heqe3. reflexivity.
  Case "e3 = false".
    remember (beq_nat n 5) as e5. destruct e5.
    SCase "e5 = true".
      apply beq_nat_eq in Heqe5.
      rewrite -> Heqe5. reflexivity.
    SCase "e5 = false". inversion eq.
Qed.

Theorem override_same : forall {X:Type} x1 k1 k2 (f : nat -> X),
    f k1 = x1 ->
    (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f eq. unfold override.
  remember (beq_nat k1 k2). destruct b.
  Case "b = true". apply beq_nat_eq in Heqb.
    rewrite <- Heqb. symmetry in eq. apply eq.
  Case "b = false". reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
    [a,b] = [c,d] ->
    [c,d] = [e,f] ->
    [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

Theorem trans_eq : forall {X:Type} (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
    [a,b] = [c,d] ->
    [c,d] = [e,f] ->
    [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c,d]). apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m. apply eq2. apply eq1.
Qed.

(*これ以上は意味不明 apply withの使い方がよくわからん*)
Theorem beq_nat_trans : forall n m p,
    true = beq_nat n m ->
    true = beq_nat m p ->
    true = beq_nat n p.
Proof.
  intros n m p eq1 eq2.
  apply beq_nat_eq in eq1. apply beq_nat_eq in eq2.
Admitted.

Definition fold_length {X:Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
    fold_length l = length l.
Proof.
  induction l as [| x l'].
  Case "l = []". unfold fold_length. simpl. reflexivity.
  Case "l = x :: l'". simpl. rewrite <- IHl'.
  unfold fold_length. simpl. reflexivity.
Qed.

Definition fold_map {X Y:Type} (f:X->Y) (l:list X) : list Y :=
  fold (fun x ys => f x :: ys) l [].

Example fold_map_test1: fold_map (fun x => evenb x) [1,2,3,4] = map (fun x => evenb x) [1,2,3,4].
Proof. reflexivity. Qed.

Theorem fold_map_correct : forall {X Y:Type} (f:X->Y) l,
    fold_map f l = map f l.
Proof.
  induction l as [| x l'].
  Case "l = []". unfold fold_map. simpl. reflexivity.
  Case "l = x :: l'". simpl. rewrite <- IHl'.
    unfold fold_map. simpl. reflexivity.
Qed.

Module MumbleBaz.

Inductive mumble : Type :=
| a : mumble
| b : mumble -> nat -> mumble
| c : mumble.
Inductive grumble (X:Type) : Type :=
| d : mumble -> grumble X
| e : X -> grumble X.

Inductive baz : Type :=
| x : baz -> baz
| y : baz -> bool -> baz.

End MumbleBaz.

Fixpoint forallb {X:Type} (f:X->bool) (l:list X) : bool :=
  match l with
  | [] => true
  | h :: t => if f h
              then forallb f t
              else false
  end.

Fixpoint existsb {X:Type} (f:X->bool) (l:list X) : bool :=
  match l with
  | [] => false
  | h :: t => if f h
              then true
              else existsb f t
  end.

Definition existsb' {X:Type} (f:X->bool) (l:list X) : bool :=
  negb (forallb (fun x => negb (f x)) l).

Theorem existsb'_correct : forall {X:Type} (f:X->bool) l,
    existsb' f l = existsb f l.
Proof.
  intros. induction l as [| x l'].
  Case "l = []". unfold existsb'. simpl. reflexivity.
  Case "l = x :: l'". unfold existsb'. simpl.
    destruct (f x).
    SCase "f x = true". simpl. reflexivity.
    SCase "f x = false". simpl. rewrite <- IHl'.
      unfold existsb'. reflexivity.
Qed.