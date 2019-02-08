Require Export ImpList.

Definition Assertion := state -> Prop.

(*
fun st => asnat (st X) = 3
状態stにおいて，asnat後のXの評価結果は3と等しい
fun st => asnat (st X) = x
状態stにおいて，asnat後のXの評価結果はxと等しい
fun st => asnat (st X) <= asnat (st Y)
状態stにおいて，asnat後のXの評価結果はasnat後のYの評価結果以下である
fun st => asnat (st X) = 3 ∨ asnat (st X) <= asnat (st Y)
状態stにおいて，asnat後のXの評価結果は3と等しいまたはasnat後のXの評価結果はasnat後のYの評価結果以下である
fun st => (asnat (st Z)) * (asnat (st Z)) <= x 
          ∧ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x)
fun st => True
状態stにおいて，真である
fun st => False 
状態stにおいて，偽である
*)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
    c / st || st' ->
    P st ->
    Q st'.

Notation "{{ P }} c" := (hoare_triple P c (fun st => True)) (at level 90) : hoare_spec_scope.
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(*
{{True}} c {{X = 5}}
事前条件が{真}であるとき，cの評価後，事後条件{Xと5が等しい}が成り立つ
{{X = x}} c {{X = x + 5)}}
事前条件が{Xとxが等しい}なら，cの評価後，事後条件{Xとx + 5が等しい}が成り立つ
{{X <= Y}} c {{Y <= X}}
事前条件が{XがY以下}なら，cの評価後，事後条件{YがX以下}が成り立つ
{{True}} c {{False}}
事前条件が{真}なら，cの評価後，事後条件{偽}が成り立つ
{{X = x}} c {{Y = real_fact x}}.
事前条件が{Xとxが等しい}なら，cの評価後，事後条件{Yとreal_fact xが等しい}が成り立つ
{{True}} c {{(Z * Z) <= x ∧ ~ (((S Z) * (S Z)) <= x)}}
事前条件が{真}なら，cの評価後，事後条件{(Z*Zがx以下)かつ(Zの次の数*Zの次の数がx以下でない)である}が成り立つ
*)

(*
valid
      {{True}} X ::= 5 {{X = 5}}
valid
      {{X = 2}} X ::= X + 1 {{X = 3}}
valid
      {{True}} X ::= 5; Y ::= 0 {{X = 5}}
invalid
      {{X = 2 ∧ X = 3}} X ::= 5 {{X = 0}}
invalid
      {{True}} SKIP {{False}}
invalid
      {{False}} SKIP {{True}}
invalid
      {{True}} WHILE True DO SKIP END {{False}}
valid
      {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}
invalid
      {{X = 1}}
      WHILE X <> 0 DO X ::= X + 1 END
      {{X = 100}} 
*)

Theorem hoare_post_true :forall (P Q : Assertion) c,
    (forall st, Q st) ->
    {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
    (forall st, ~(P st)) ->
    {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.
Qed.

(*
     {{ ? }} SKIP {{ X = 5 }}
X = 5

     {{ ? }} X ::= Y + Z {{ X = 5 }}
Y + Z = 5

     {{ ? }} X ::= Y {{ X = Y }}
TRUE

     {{ ? }}
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}
Z = 4 /\ W = 3

     {{ ? }}
     X ::= 5
     {{ X = 0 }}
FALSE

     {{ ? }}
     WHILE True DO X ::= 0 END
     {{ X = 0 }}
FALSE
*)

(*
Theorem hoare_asgn_firsttry :
  forall (Q : aexp -> Assertion) V a,
    {{fun st => Q a st}} (V ::= a) {{ fun st => Q(AId V) st}}.
*)

Definition assn_sub V a Q : Assertion :=
  fun (st : state) =>
    Q (update st V (aeval st a)).

Theorem hoare_asgn : forall Q V a,
    {{assn_sub V a Q}} (V ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q V a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.
Qed.

Example assn_sub_example :
  {{fun st => 3 = 3}}
    (X ::= (ANum 3))
  {{fun st => asnat (st X) = 3}}.
Proof.
  assert ((fun st => 3 = 3) = 
         (assn_sub X(ANum 3) (fun st => asnat (st X) = 3))).
  Case "Proof of assertion".
    unfold assn_sub. reflexivity.
    rewrite -> H. apply hoare_asgn.
Qed.

Theorem hoare_asgn_eq : forall Q Q' V a,
    Q' = assn_sub V a Q ->
    {{Q'}} (V ::= a) {{Q}}.
Proof.
  intros Q Q' V a H. rewrite H.
  apply hoare_asgn.
Qed.

(*
{{ X + 1 <= 5 }} X ::= X + 1 {{ X <= 5 }}
*)
Example hoare_asgn_examples1 :
  {{fun st => asnat (st X) + 1 <= 5}}
  (X ::= (APlus (AId X) (ANum 1)))
  {{fun st => asnat (st X) <= 5}}.
Proof.
  apply hoare_asgn_eq.
  unfold assn_sub. reflexivity.
Qed.

(*
{{ 0 <= 3 ∧ 3 <= 5 }} X ::= 3 {{ 0 <= X ∧ X <= 5 }}
*)

Example hoare_asgn_examples2 :
  {{fun st => 0 <= 3 /\ 3 <= 5}}
  (X ::= (ANum 3))
  {{fun st => 0 <= asnat (st X) /\ asnat (st X) <= 5}}.
Proof.
  apply hoare_asgn_eq.
  unfold assn_sub. reflexivity.
Qed.

Theorem hoare_asgn_weakest : forall P V a Q,
    {{P}} (V ::= a) {{Q}} ->
    forall st, P st -> assn_sub V a Q st.
Proof.
  intros.
  unfold assn_sub.
  unfold hoare_triple in H.
  (*わからん*)

Admitted.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
    {{P'}} c {{Q'}} ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q. apply (Hht st st'). assumption.
  apply HPP'. assumption.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
    {{P'}} c {{Q}} ->
    (forall st, P st -> P' st) ->
    {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  apply hoare_consequence with (P' := P') (Q' := Q);
    try assumption.
  intros st H. apply H.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
    {{P}} c {{Q'}} ->
    (forall st, Q' st -> Q st) ->
    {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  apply hoare_consequence with (P' := P) (Q' := Q');
    try assumption.
  intros st H. apply H.
Qed.

Example hoare_asgn_example1 :
  {{fun st => True}}
  (X ::= (ANum 1))
  {{fun st => asnat (st X) = 1}}.
Proof.
  apply hoare_consequence_pre with (P' := (fun st => 1 = 1)).
  apply hoare_asgn_eq. reflexivity.
  intros st H. reflexivity.
Qed.

Example hoare_asgn_example1' :
  {{fun st => True}}
  (X ::= (ANum 1))
  {{fun st => asnat (st X) = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn_eq. reflexivity.
  intros st H. reflexivity.
Qed.

Theorem hoare_skip : forall P,
    {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
    {{Q}} c2 {{R}} ->
    {{P}} c1 {{Q}} ->
    {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); try assumption.
Qed.

Example hoare_asgn_example3 : forall a n,
    {{fun st => aeval st a = n}}
    (X ::= a; SKIP)
    {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  Case "right part of seq".
    apply hoare_skip.
  Case "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1); Y ::= (ANum 2))
  {{fun st => asnat (st X) = 1 /\ asnat (st Y) = 2}}.
Proof.
  eapply hoare_seq.
  Case "right part of seq".
    apply hoare_asgn.
  Case "left part of seq".
    eapply hoare_consequence_pre.
    apply hoare_asgn. intros st H.
    unfold assn_sub. apply conj.
    SCase "left". reflexivity.
    SCase "right". reflexivity.
Qed.