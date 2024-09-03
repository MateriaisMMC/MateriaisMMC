Section Questao_1.
Lemma primeira: forall n m, (n=0 /\ 0=m) -> S n = S m.
Proof.
intros.
destruct H.
rewrite H.
rewrite H0.
congruence.
Qed.
End Questao_1.

Section Questao_2.

Definition c_2 := fun f:nat -> nat => fun x:nat => f (f x).
Check c_2.
Eval compute in c_2 S 0.



Lemma alinea_b: forall n, c_2 S n = S (S n).
Proof.
intros.
f_equal.
reflexivity.
Qed.


Lemma alinea_c: forall m n, c_2 S (m + n) = m + (S (S n)).
Proof.
induction m.
intros.
compute.
reflexivity.
intro.
specialize IHm with n.
compute.
fold plus.
f_equal.
apply IHm.
Qed.
End Questao_2.
Require Import Classical.

Section Questao_3.

Inductive impar: nat -> Prop :=
imp_1: impar 1| imp_n: forall n, impar n -> impar (S (S n)).

Lemma alinea_a3: impar 3 /\ ~impar 4.
Proof.
split.
apply imp_n.
apply imp_1.
intro.

inversion H.
inversion H1.
inversion H3.
Qed.

Lemma aline_b3: forall n, impar n <-> impar (S (S n)).
Proof.
split.
intro.
apply imp_n.
assumption.
intro.
inversion H.
apply H1.
Qed.

Lemma aline_c3: forall n, impar n -> ~ impar (S n).
Proof.

intro.
induction n.
intro.
inversion H.
intro.

assert (H1 : ~impar n \/ ~impar (S n)).
left.
intro.
apply IHn in H0.
contradiction.
intro.
inversion H0.

destruct H1.
contradiction.

contradiction.


Qed.



Lemma exemplo_a1 : forall p q r:Prop, (p-> (q -> r)) <-> ((p/\q)->r).
Proof.
intros.

split.
2:{
intros.
apply H.
split.
apply H0.
apply H1.
}
intros.
destruct H0.
specialize (H H0 H1).
apply H.  
Qed.
Lemma exemplo_a : forall p q r:Prop, (p-> (q -> r)) <-> ((p/\q)->r).
Proof.
intros.
split.
intro.
intro.
destruct H0.
specialize (H H0 H1).
apply H.
intros.
apply H.
split.
apply H0.
apply H1.
Qed.

End Questao_3.
