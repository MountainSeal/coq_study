Require Export Poly.

Theorem double_injective_FAILED : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0". simpl. intros eq. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = 0". inversion eq.
    SCase "m = S m'".
      assert (n' = m') as H.
      SSSCase "Proof of assertion".
Admitted.

Theorem double_injective' : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". simpl. intros m eq. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'". intros m eq. destruct m as [| m'].
    SCase "m = 0". inversion eq.
    SCase "m = S m'".
      assert (n' = m') as H.
      SSCase "Proof of assertion". apply IHn'.
        inversion eq. reflexivity.
        rewrite -> H. reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  Case "m = 0". simpl. intros n eq. destruct n as [| n'].
    SCase "n = 0". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
        apply IHm'. inversion eq. reflexivity.
      rewrite -> H. reflexivity.
Qed.

Theorem plus_n_n_injective_take2 : forall n m,
    n + n = m + m ->
    n = m.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m'].
  Case "m = 0". simpl. intros n eq.
    destruct n as [| n'].
    SCase "n = 0". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq.
    destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'". simpl in eq.
      rewrite -> plus_comm in eq. simpl in eq. rewrite <- double_plus in eq.
      rewrite -> plus_comm in eq. simpl in eq. rewrite <- double_plus in eq.
      inversion eq. apply double_injective' in H0.
      rewrite -> H0. reflexivity.
Qed.

Theorem index_after_self_length : forall (X:Type) (l:list X),
    index (S (length l)) l = none.
Proof.
  intros. induction l as [| x l'].
  Case "l = []". simpl. reflexivity.
  Case "l = x :: l'". simpl. apply IHl'.
Qed.

Theorem index_after_last : forall (n:nat) (X:Type) (l:list X),
    length l = n ->
    index (S n) l = none.
Proof.
  intros. generalize dependent n.
  induction l as [| x l'].
  Case "l = []". simpl. reflexivity.
  Case "l = x :: l'". intros n H. simpl. simpl in H.
    destruct n as [| n'].
    SCase "n = 0". inversion H.
    SCase "n = S n'". inversion H. apply IHl'. reflexivity.
Qed.

Theorem length_snoc''' : forall (n : nat) (X : Type)
                                (v : X) (l : list X),
    length l = n ->
    length (snoc l v) = S n.
Proof.
  intros. generalize dependent n.
  induction l as [| x l'].
  Case "l = []". intros. rewrite <- H. reflexivity.
  Case "l = x :: l'". intros. simpl.
    destruct n as [| n'].
    SCase "n = 0". inversion H.
    SCase "n = S n'". apply eq_remove_S. apply IHl'.
      simpl in H. inversion H. reflexivity.
Qed.

Theorem app_length : forall (X:Type) (l1 l2:list X),
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros. induction l1 as [| x l1'].
  Case "l1 = []". reflexivity.
  Case "l1 = x :: l1'". simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem app_length_cons : forall (X:Type) (l1 l2:list X)
                                 (x:X) (n:nat),
    length (l1 ++ (x :: l2)) = n ->
    S (length (l1 ++ l2)) = n.
Proof.
  intros. generalize dependent n.
  induction l1 as [| v l1'].
  Case "l1 = []". intros. simpl. simpl in H. apply H.
  Case "l1 = v :: l1'". intros.
    destruct n as [| n'].
    SCase "n = 0". inversion H.
    SCase "n = S n'". apply eq_remove_S. simpl.
      apply IHl1'. simpl in H. inversion H. reflexivity.
Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
    length l = n ->
    length (l ++ l) = n + n.
Proof.
  intros. generalize dependent n.
  induction l as [| x l'].
  Case "l = []". intros. inversion H. simpl. reflexivity.
  Case "l = x :: l'". intros.
    destruct n as [| n'].
    SCase "n = 0". inversion H.
    SCase "n = S n'".
      (* ダメみたいですね(諦観) *)
      (*simpl. apply eq_remove_S.
      rewrite -> plus_comm. simpl.
      inversion H.*)
      inversion H. apply app_length.
Qed.