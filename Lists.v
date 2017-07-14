Require Export Basics.

Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst(p : natprod) : nat :=
  match p with
  |pair x y => x
  end.

Definition snd(p :natprod) : nat :=
  match p with
  |pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Eval simpl in (fst (3,4)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  intros p. destruct p as (n,m). simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as (n,m). simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)(at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition l_123' := 1 :: (2 :: (3 :: nil)).
Definition l_123'' := 1 :: 2 :: 3 :: nil.
Definition l_123''' := [1,2,3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  |O => nil
  |S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  |nil => O
  |h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  |nil => l2
  |h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.
Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

Definition hd (default:nat)(l:natlist) : nat :=
  match l with
  |nil => default
  |h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  |nil => nil
  |h :: t => t
  end.

Example test_hd1:             hd 0 [1,2,3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tail:            tl [1,2,3] = [2,3].
Proof. reflexivity.  Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if beq_nat h O then nonzeros t else h :: (nonzeros t)
  end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t =>
    match (oddb h) with
    | true  => h :: (oddmembers t)
    | false => oddmembers t
    end
  end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l : natlist) : nat :=
  match l with
  | nil    => 0
  | h :: t =>
    match (oddb h) with
    | true  => S (countoddmembers t)
    | false => countoddmembers t
    end
  end.

Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, nil => nil
  | nil, _   => l2
  | _  , nil => l1
  | h1 :: t1, h2 :: t2 =>
    h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4: alternate [] [20,30] = [20,30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil    => 0
  | h :: t =>
    match (beq_nat v h) with
    | true  => S (count v t)
    | false => count v t
                     end
  end.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1,4,1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  match (count v s) with
  | O   => false
  | S _ => true
  end.

Example test_member1: member 1 [1,4,1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1,4,1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => 
    match (beq_nat v h) with
    | true  => t
    | false => h :: (remove_one v t)
    end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
    match (beq_nat v h) with
    | true  => remove_all v t
    | false => h :: (remove_all v t)
    end
  end.

Example test_remove_all1:          count 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2:          count 5 (remove_all 5 [2,1,4,1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3:          count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4:          count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1, s2 with
  | nil, nil  => true
  | _,   nil  => false
  | nil, _    => true
  | h1::t1, _::t2 =>
    match (count h1 s2) with
    | O   => false
    | S _ => subset t1 (remove_one h1 s2)
    end
  end.

Example test_subset1: subset [1,2] [2,1,4,1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
Proof. simpl. reflexivity. Qed.

Theorem nil_app : forall l:natlist,
    [] ++ l = l.
Proof.
  reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
    pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    simpl. reflexivity.
  Case "l = cons n l'".
    simpl. reflexivity.
  Qed.

Theorem app_ass : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    simpl. reflexivity.
  Case "l1 = n l1'".
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = l1'".
    simpl. reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem length_snoc : forall n : nat, forall l : natlist,
      length (snoc l n) = S (length l).
Proof.
  intros n l.
  induction l as [| n' l'].
  Case "l = nil".
    simpl. reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
    length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    simpl. reflexivity.
  Case "l = n :: l'".
    simpl. rewrite -> length_snoc. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_nil_end : forall l : natlist,
    l ++ [] = l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    simpl. reflexivity.
  Case "l = n :: l'".
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem rev_snoc : forall l : natlist, forall n : nat,
          rev (snoc l n) = n :: rev l.
Proof.
  intros l n. induction l as [| n' l'].
  Case "l = nil".
    simpl. reflexivity.
  Case "l = n' :: l'".
    simpl. rewrite -> IHl'. simpl. reflexivity.
Qed.
  
Theorem rev_involutive : forall l : natlist,
    rev (rev l) = l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    simpl. reflexivity.
  Case "l = n :: l'".
    simpl. rewrite -> rev_snoc. rewrite -> IHl'. reflexivity.
Qed.

Theorem snoc_rev : forall l1 l2 : natlist, forall n : nat,
          snoc (l1 ++ rev l2) n = l1 ++ snoc (rev l2) n.
Proof.
  intros l1 l2 n. induction l1 as [|n' l1'].
  Case "l1 = nil".
    simpl. reflexivity.
  Case "l1 = n :: l1'".
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
    rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    simpl. rewrite -> app_nil_end. reflexivity.
  Case "l1 = n :: l1'".
    simpl. rewrite -> IHl1'.
    rewrite -> snoc_rev. reflexivity.
Qed.

Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  induction l1 as [| n l1'].
  Case "l1 = nil".
    simpl. rewrite -> app_ass. reflexivity.
  Case "l1 = n :: l1'".
    simpl. rewrite <- app_ass. rewrite <- app_ass. reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
    snoc l n = l ++ [n].
Proof.
  intros l n.
  induction l as [| n' l'].
  Case "l = nil".
    simpl. reflexivity.
  Case "l = n' l'".
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_nil : forall l : natlist,
    l ++ [] = l.
Proof.
  intros l. induction l as [|n l'].
  Case "l = nil".
    simpl. reflexivity.
  Case "l = n :: l'".
    simpl. rewrite -> IHl'. reflexivity.
Qed.

(*わかりません(絶望)*)
(*三章でif文のdestructを知って使ったらこれだよ☆*)
(*恐らくnonzerosの実装に問題があるためこのようにせざるを得ないのだと思います*)
Lemma nonzeros_length : forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  Case "l1 = []". reflexivity.
  Case "l1 = n :: l1'".
    simpl. destruct (beq_nat n 0).
    SCase "beq_nat n 0 = true". rewrite -> IHl1'. reflexivity.
    SCase "beq_nat n 0 = false".
      rewrite -> IHl1'. simpl. reflexivity.
Qed.

End NatList.