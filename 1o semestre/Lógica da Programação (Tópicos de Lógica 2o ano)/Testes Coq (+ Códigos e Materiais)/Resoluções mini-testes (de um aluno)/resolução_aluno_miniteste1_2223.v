(* Pode conter ERROS !!! *)

Section Questao1.

Variables A B C: Prop.

Lemma q1_a : (A -> (B -> C)) -> (B -> (A -> C)).
Proof.
intros.
apply H.
assumption.
assumption.
Qed.

Lemma q1_b : (A \/ (B /\ C)) -> ((A \/ B) /\ (A \/ C)).
Proof.
intros.
split.
destruct H.
left.
assumption.
destruct H.
right.
assumption.
destruct H.
left.
assumption.
destruct H.
right.
assumption.
Qed.

Lemma q1_c : (~A /\ B) -> ~(A \/ ~B).
Proof.
intros.
intro.
destruct H.
destruct H0.
contradiction.
contradiction.
Qed.

End Questao1.

Section Questao2.

Variable D: Set.
Variable c: D. (*constante para aplicar exists c.*)
Variable P Q: D -> Prop.
Variable f : D -> D.

Lemma q2: (forall(x:D), (P x) -> (Q (f x))) -> (P(c) -> (exists(x:D), P x /\ Q (f x))).
Proof.
intros.
exists c.
split.
assumption.
apply H.
assumption.
Qed.

End Questao2.

Section Questao3.

Variable D: Set.
Variable c: D. (*constante para aplicar exists c.*)
Variable P Q: D -> Prop.
Variable f : D -> D.

Require Import Classical. 
(*Check NNPP.*) 

Lemma q: (forall(x:D), (P x -> Q x)) -> (forall(x:D), (~P x \/ Q x)).
Proof.
intros.
apply NNPP.
intro.
assert(H1: P x).
apply NNPP.
intro.
apply H0.
left.
assumption.
assert(H2: ~Q x).
intro.
apply H0.
right.
assumption.
apply H2.
apply H.
assumption.
Qed.

End Questao3.


