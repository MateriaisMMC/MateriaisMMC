(*2º mini-teste *)
(* Tem ERROS !!! *)


(*Questão 1*)
Section questao1.

Lemma q1: forall m n k l, (m=S n /\ S k=l /\ k=n) -> m=l.
Proof.
intros.
destruct H.
destruct H0.
rewrite H.
rewrite <- H1.
rewrite H0.
reflexivity.
Qed.

End questao1.

(*-------------------------------------------------------*)
(*Questão 2*)
Section questao2.

Definition c_1:= fun f:nat->nat => fun x:nat => f x.

(*alínea a*)
Section questao2_a.

(*termo (i)*)
Eval compute in (c_1 S).
(* Tipo: nat -> nat ; Forma Normal: fun x : nat => S x *)

(* O resultado obtido para o termo (i) mostra que a função c_1 adiciona ao argumento
que recebe o valor numérico 1. *)

Eval compute in (c_1 S 1).
(* Tipo: nat ; Forma Normal: 2 *)

(* Já o resultado obtido para o termo (ii) mostra que quando o argumento da função
 c_1 é 1, este dá um resultado igual a 2. *)

End questao2_a.

(*alínea b*)
Section questao2_b.

Lemma q2_b: forall m n, (c_1 S m) + n = m +1 +n.
Proof.
induction m.

intro.
compute.
reflexivity.

intro.
compute.
fold plus.
f_equal.
compute in IHm.
fold plus in IHm.
rewrite IHm.
reflexivity.
Qed.

End questao2_b.

End questao2.

(*--------------------------------------------------------*)
(*Questão 3*)
Section questao3.

Definition teste_0 := fun n:nat =>
  match n with
  | 0 => 1
  | S m => 0
  end.

(*demosntração sem o uso de indução*)
Lemma q3: forall n, (exists m, n = S m) -> teste_0 n=0.
Proof.
intros.
destruct H.
rewrite H.
compute.
reflexivity.
Qed.

End questao3.

(*--------------------------------------------------------*)
(*Questão 4*)
Section questao4.

Inductive par: nat -> Prop :=
  par0: par 0 | parS : forall n:nat, par n -> par (S (S n)).

Inductive impar: nat -> Prop :=
  imp1: impar 1 | impS : forall n, impar n -> impar (S (S n)).

(*alínea a*)
Section questao4_a.

Lemma par_4_e_4_nao_impar: par 4 /\ ~impar 4.
Proof.
split.

apply parS.
apply parS.
apply par0.

intro.
inversion H.
inversion H1.
inversion H3.
Qed.

End questao4_a.

(*alínea b*)
Section questao4_b.

Lemma q4_b: forall n, par n -> impar (S n).
Proof.
induction n.
intros.
destruct H.

apply imp1.
apply impS.
inversion H.
apply imp1.

rewrite H1.

(*2: {
  intros.
  destruct IHn.
  Admitted.
}*)

(*INCOMPLETO*)

Admitted.

End questao4_b.

(*alínea c*)
Section questao4_c.

Lemma q4_c: forall n, par n \/ impar n.
Proof.
induction n.
left.
apply par0.

destruct IHn.
right.
inversion H.
subst.
apply imp1.
apply impS.

(*2: {
  left.
  destruct H.
  apply parS.
  apply par0.
  apply parS.
  Admitted.
}*)

(*INCOMPLETO*)
Admitted.

End questao4_c.

End questao4.