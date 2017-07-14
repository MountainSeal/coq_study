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
  Case "l = x :: l'". intros n H. simpl.
    rewrite <- H. simpl. apply index_after_self_length.
    (*
正直最後のapplyのやり方に納得がいかない．
だってlの帰納法を使うまでも無く解けてしますやり方だから，
lの帰納法を使うという練習問題としての意味がなくなってしまう．
     *)
Qed.