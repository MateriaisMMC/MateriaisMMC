
(*Criar uma secção*)
Section Questao1.

(* 1ª questão do mini-teste do ano passado *)
Variables p0 p1 p2:Prop.

(* Fórmula da questão*)
Lemma alinea_a: (p0 -> (p1 -> p2)) -> (p1 -> (p0 -> p2)).

(*p2 será a conclusão, com duas hipóteses*)

(*Iniciar a demonstração*)
Proof.
intros.
apply H.
assumption.
assumption.
Qed.

Lemma alinea_a_2: (p0 -> (p1 -> p2)) -> (p1 -> (p0 -> p2)).

(*alternativa*)
Proof.
intros.
apply H.
assumption.
exact H1.
assumption.
Qed.

Lemma alinea_a_3: (p0 -> (p1 -> p2)) -> (p1 -> (p0 -> p2)).

(*alternativa*)
Proof.
intros.
apply H.
trivial.
trivial.
Qed.

Lemma alinea_a_new: (p0 -> (p1 -> p2)) -> (p0 -> (p1 -> (p0 -> p2))).
Proof.
intros.
apply H.
trivial.
trivial.
Qed.

Print alinea_a.

Lemma alinea_b: (p0 \/ (p1 /\ p2) -> ((p0 \/ p1) /\ (p0 \/ p2))).
Proof.
intro.
split. (*partir em dois sub-problemas*)
destruct H.
left;assumption.
destruct H.
right;assumption.
destruct H.
left;assumption.
destruct H.
right;assumption.
Qed.

Print alinea_b.

Lemma alinea_c: (~p0 /\ p1) -> ~(p0 \/ p1).
Proof.
intros.
intro.
destruct H0.
destruct H.
apply H.
assumption.
Qed.

Lemma alinea_c_2: (~p0 /\ p1) -> ~(p0 \/ ~p1).
Proof.
intros.
intro.
destruct H0.
destruct H.
apply H.
assumption.
destruct H.
contradiction.
Qed.

(*Declaração do tipo de linguagem*)

Variable D:Set. (*domínio da L-estrutura*)

Variable f:D -> D. (*símbolo de função unário*)
Variables P Q: D -> Prop. (* 2 símbolos de relação unários - vão produzir fórmulas*)
Variable c:D. (*uma constante é um elemento de D*)

Lemma ex_2: (forall x, ((P x) -> Q (f x))) -> (P c -> exists x, (P x /\ Q (f x))).
Proof.
intro.
intro.
exists c.
split.
assumption.
apply H.
assumption.
Qed.


Require Import Classical.

Check NNPP. (*redução ao absurdo*)

Lemma ex_3: (forall x, (P x -> Q x)) -> forall x, ~ P x \/ Q x.
Proof.
intro.
intro.
apply NNPP.
intro.
assert(H1:P x).
apply NNPP.
intro.
apply H0.
left;assumption.
assert(H2: ~Q x).
intro;
apply H0.
right;assumption.
apply H2.
apply H.
assumption.
Qed.
