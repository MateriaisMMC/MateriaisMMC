(* Com ERROS!!! *)

Section Questao1.

Variables p0 p1 p2: Prop.

Lemma a: (p0 -> (p1 -> p2)) -> ((p0 -> p1) -> (p0 -> p2)).
Proof.
intros.
apply H.
assumption.
apply H0.
assumption.
Qed.

Lemma b: ((p0 \/ p1) /\ (~p1 \/ p2)) -> (p0 \/ p2).
Proof.
intros.
destruct H.
destruct H.
destruct H0.
left.
assumption.
right.
assumption.
destruct H0.
contradiction.
right.
assumption.
Qed.

Lemma c: (~p0 /\ p1) <-> (~~~p0 /\ p1). (* como substituição da questão 3*)
Proof.
split.
intros.
destruct H.
split.
intro.
contradiction.
assumption.
intros.
destruct H.
split.
intro.
destruct H.
intro.
contradiction.
assumption.
Qed.

End Questao1.

(*----------------------------*)

Section Questao2.

Variable D: Set.
Variable c : D. 
Variable P: D -> Prop.
Variable f : D -> D.

Lemma q2 : ((exists (x:D), P x) /\ (forall(x:D), (P x -> (P (f (f x)) /\ ~ P (f x))))) 
-> ((exists(y:D), ~ P (f y)) /\ (exists(y:D), P (f y))).
Proof.
intros.
destruct H.
destruct H.
split.
exists c.
apply H0.
specialize H0 with c.
destruct H0.
3 : {
  exists (f c).
  apply H0.
  specialize H0 with c.
  destruct H0.
  admit.
  admit.
}
admit.
admit.
Admitted.

End Questao2.

(* Não consegui resolver a questão 3, admiti a questão 1-c) como a resposta ! *)

(*----------------------------*)

(*Section Questao3.

Variable D: Set.
Variables c  : D. 
Variable R: D -> D -> Prop.

Require Import Classical.
(* Check NNPP. *)

Lemma q3 : (forall(x:D), ~(forall(y:D), R x y)) -> (forall(x:D),(exists(y:D), ~ R x y)).
Proof.
intros.
apply NNPP.
intro.
destruct H0.
exists c.
intro.
assert(H1: ).
Qed.

End Questao3.*)





