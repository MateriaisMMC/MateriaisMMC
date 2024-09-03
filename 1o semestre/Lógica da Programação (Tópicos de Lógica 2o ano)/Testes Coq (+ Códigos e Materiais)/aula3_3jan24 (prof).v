(*Aula 3 janeiro 2024*)

(*****************************************************************)


(*Os naturais em Coq - "tipo indutivo" pré-definido, 
com dois "construtores", "0" e "S".*)

Check nat.
Print nat.
Check 0.
Check S.
Check S 0.

(*****************************************************************)

Section Igualdade.

(*A relação de igualdade é obtida através do tipo indutivo (e polimórfico) "eq",
podendo usar-se a notação habitual, com o símbolo "=".*)

Check 0 = 0.

Check eq.
Print eq.

Lemma zero_igual_zero: 0=0.
Proof.

reflexivity.
(*A aplicação da tática "reflexivity" é bem sucedida quando ambos os lados da igualdade
são "definicionalmente iguais", ou seja, têm a mesma "forma normal" relativamente
a um certo conjunto de regras -como por exemplo a "regra beta".*) 

Qed.

Print zero_igual_zero.

Variable f: nat -> nat.
Hypothesis f00: f 0 =0.
(*O mesmo efeito do comando "Hypothesis" poderia ser obtido com a o comando
"Variable".*)

Lemma igual1: forall k:nat, k=0 -> f k=k.
Proof.
intros.

rewrite H.
(*A tática "rewrite" possibilita a utilização de uma igualdade (no caso "H"), 
substituindo no goal subtermos correspondentes ao lado esquerdo da igualdade 
pelo correspondente lado direito.*)

assumption.
Qed.

Lemma igual2: forall k:nat, 0=k -> f k=k.
Proof.
intros.

rewrite <- H.
(*O símbolo "<-" indica que a igualdade deverá ser utilizada 
da direita para a esquerda.*)

apply f00.
Qed.

Lemma igual3: forall k m:nat, 0=k /\ k=m -> f k =m.
Proof.
intros.
destruct H.

replace m with 0.
(*A tática "replace" substitui um termo por outro no goal 
(no caso, subsitui "m" por "0"), gerando como novo subgoal 
a igualdade entre estes termos.*)

rewrite <- H.
assumption.
rewrite H.
assumption.
Qed.

(*Definições *)

Definition um:= S 0.
(*O comando "Definition" permite associar um identificador 
(no caso "um") a um dado termo (no caso "S 0").*)

Check um = S 0.

Lemma um_igual_S0: um = S 0.
Proof.

unfold um.
(* A tática "unfold" permite substituir no goal um identificador
introduzido através de uma definição pelo respetivo termo -em Coq,
esta transformação é designada "redução-delta"*)

(*reflexivity.*)
congruence.
(* Esta tática automática implementa um certo algoritmo para 
decidir igualdades, que em particular assume que a igualdade é uma
congruência e pode tirar partido de igualdades nas hipóteses, 
falhando caso o algoritmo não consiga "resolver" a igualdade.*)

Qed.

Lemma um_diferente_0: ~ um=0.
Proof.
intro.

unfold um in H.
(*A tática "unfold" -tal como muitas outras táticas- também 
pode ser aplicada a uma dada hipótese (neste caso "H").*)

discriminate.
(*Esta tática prova um goal caso detete que uma das hipóteses 
corresponde a uma igualdade (estruturalmente) impossível sobre 
um tipo indutivo, o que neste caso sucede com "H" 
(dado que os construtores mais externos em cada um dos lados
da igualdade são distintos). A partir desta hipótese "H", outras táticas, 
tais como "congruence" ou "inversion" - a ver adiante-,
produziriram efeito análogo.*)

Qed.

End Igualdade.

(*****************************************************************)

Section Beta_reducao.

(*As exemplificações que se seguem requerem um tipo, que designaremos por
"tau" -recorde-se que em Coq qualquer expressão tem que ser tipificável-,
mas podem ser replicadas com qualquer tipo concreto, como por exemplo
"nat".*)

Variable tau:Type.
(*Definition tau:= nat.*)

Variable x y:tau.
Variable z: tau -> tau.

(*Seguem-se definições dos combinadores I e K. O comando "Let"
produz uma definição local à secção.*)
Let I:= fun x:tau => x.
Check I.
Let K:=fun x y:tau => x.
Check K.

Eval compute in I (I x).
(*O comando "Eval" efetua "reduções" no termo indicado ("I (I x)", no caso).
As "regras" a considerar no processo de redução e a "estratégia de redução" são
neste caso especificadas através da tática "compute". Entre outras, esta tática
considera a "regra beta" e a "regra delta" - recorde-se que
a segunda corresponde ao "unfolding" de definições.*)  
   
Eval compute in K (I x) y.

Eval cbv beta in K (I x) y.
(*No caso anterior, a tática "cbv" especifica que apenas deverá ser
considerada a regra "beta". Note-se que no termo em causa
não há qualquer beta-redex. Estes tornar-se-ão visíveis 
apenas com o "unfolding" de "K"/"I", conforme a exemplificação seguinte.
*)  
Eval cbv delta in K (I x) y.
Eval cbv beta delta in K (I x) y.

(*A tática "cbv" está associada a uma estratégia de avaliação de termos 
designada "chamada-por-valor". O Coq disponibiliza táticas associadas
a outras estratégias de avaliação, tais como "cbn", associada à estratégia 
"chamada-por-nome". Por exemplo, estas duas estratégias têm comportamentos 
distintos no caso que se segue.*)
Eval cbv in z (I x).
Eval cbn in z (I x).


Lemma igualdade_atraves_beta_reducao: I x = K (I x) x.
Proof.

compute.
(*A tática "compute" calcula, em geral, a "forma normal do goal",
normalisando os termos envolvidos no goal.*) 

reflexivity.
Qed.

(*Os primeiros numerais de Church*)

Definition c_zero:= fun f:tau->tau=> fun x:tau => x.
Definition c_um:= fun f:tau->tau=> fun x:tau => f x.
Check c_um.
Definition c_dois:= fun f:tau->tau => fun x:tau => f (f x).
Check c_dois.

(*Operação sucessor em numerais de Church*)

Definition succ:= fun n:(tau -> tau) -> tau -> tau =>
fun f:tau->tau=> fun x:tau => f (n f x).

Check succ.

Eval compute in succ c_zero.
Eval compute in succ c_um.

Lemma ss0_igual_s1: succ (succ c_zero)= (succ c_um).
Proof.
compute.
reflexivity.
Qed.

End Beta_reducao.

(*****************************************************************)

Section Tipos_indutivos.

(*Um tipo indutivo é caracterizado pelo seu conjunto de construtores.
Um dos tipos indutivos pré-definido pelo Coq corresponde ao conjunto dos Booleanos.*) 
Check bool.
Print bool.
(* Os dois construtores dos Booleanos são "true" e "false". Estes construtores 
não devem ser confundidos com as proposições "True" e "False", 
também elas dadas indutivamente.*)
Check True. 
Check False.
Print True.
Print False. 


Lemma True_teorema: True.
Proof.

apply I.
(*Note-se que, neste caso, "I" é referente ao único 
construtor do tipo indutivo "True".*)
Qed.

Lemma Negacao_False_teorema:~False.
Proof.
intro H.
exact H.
Qed.


(*Definamos a nossa própria cópia dos Booleanos. *) 

Inductive Bool : Set:= true
  |false .

(*Os construtores true e false foram redefinidos, sendo agora construtores 
deste novo tipo Bool.*)

Check true.

(*Para cada tipo indutivo, o Coq gera automaticamente um conjunto de 
"princípios de indução", um dos quais para provar propriedades quantificadas 
universalmente sobre Bool.*)
Check Bool_ind.


Lemma bool_binario: forall b:Bool, b=true \/ b=false.
Proof.
induction b.
(* A tática "induction" aplica o princícpio de indução associado ao tipo de "b" 
(neste caso "Bool"), gerando um subgoal por cada um dos respetivos construtores.
A tática "induction" tem comportamento semelhante ao "destruct", com a diferença 
de que "induction" gera adicionalmente eventuais hipóteses de indução.
Uma outra tática que produziria, neste caso, um efeito semelhante seria "elim".*) 

left.
reflexivity.
right.
reflexivity.
Qed.

Lemma absurdo_true_igual_false: 
forall A:Prop, true=false ->A.
Proof.
intros.
discriminate H.
Qed.


(*Recordemos a definição indutiva do tipo pré-definido pelo
Coq para os naturais.*)
Print nat.

(*O princípio de indução para os naturais 
gerado automaticamente pelo Coq corresponde ao
habitual princípio de indução.*)
Check nat_ind.

(*A função soma em naturais está pré-definida em Coq, com a
designação "plus", que, na verdade, é uma abreviatura para a função 
"add" definida no módulo "Nat". A usual notação infixa, através
do símbolo "+", também pode ser utilizada.*)
Check plus.
Print plus.
Print Nat.add.
(*O comando "fix" -abreviatura de "fixpoint"- providencia um mecanismo para 
definição recursiva de funções sobre tipos indutivos, onde também é permitido 
"pattern-matching". No caso de "add", a recursão é sobre o 1º argumento "n", 
visível na indicação "{struct n}". Na verdade, neste caso, mesmo sem esta 
indicação, o Coq aceitaria esta definição recursiva, observando que a 
única invocação recursiva de "add" ocorre com um 1º argumento ("p") 
"estruturalmente menor" que "n" (dado ocorrer no caso em que "n= S p")
e que não poderia originar computações infinitas. *)

Eval compute in plus 2 3.
(*Note-se que a tática "compute" também considera reduções relativas 
a funções recursivas e pattern-matching.*) 

Eval cbv delta in plus 2 3.
Eval cbv delta fix in plus 2 3.
Eval cbv delta fix beta in plus 2 3.
Eval cbv delta fix beta iota in plus 2 3.

Lemma zero_neutro_esq: forall n, plus 0 n = n.
Proof.
intro.
compute.
reflexivity.
Qed.

Lemma zero_neutro_dir: forall n,  n + 0 = n.
Proof.
(*intro. compute.*)

induction n.
(* A tática "induction" aplica o princípio de indução associado ao 
tipo indutivo do argumento "n" - que neste caso corresponde ao usual 
princípio de indução para os  naturais.*)

(*caso 0*)
compute. reflexivity.

(*caso S n*)
compute.

fold plus.
(*Neste caso, a tática "fold" procurá reverter reduções associadas ao "unfold" 
da função "plus" - que, recorde-se, é sinónimo para "add"/"+".*)

rewrite IHn.
reflexivity.
Qed.


Lemma suc_prop1: forall m n, (S m) + n= S (m+n).
Proof.
intros.
compute.
fold plus.
reflexivity.
Qed.

Lemma suc_prop2: forall m n, m + S n= S (m+n).
Proof.
induction m.

(*caso 0*)
intro.
compute.
reflexivity.

(*caso S n*)
intro.
unfold plus at 1.
(*Neste caso, será efetuado "unfold" apenas da 1ª ocorrência de "plus"/"+".*)

fold plus.

f_equal.
(*Uma vez que em ambos os lados da igualdade o construtor mais externo é o mesmo ("S"), 
a tática "f_equal" reduz a igualdade à igualdade dos respetivos argumentos.*)

rewrite IHm.
apply suc_prop1.
Qed.

Lemma soma_comutativa: forall m n, m + n = n + m.
Proof.

induction m.

(*caso 0*)

unfold plus at 1.
intro.

symmetry.
(*Esta tática apela à simetria da relação de igualdade.*)

apply zero_neutro_dir.

(*caso S n*)

intro.
unfold plus at 1.
fold plus.
rewrite IHm.
symmetry.
apply suc_prop2.
Qed.

End Tipos_indutivos.


(*****************************************************************)

Section Predicados_indutivos.

Inductive par : nat -> Prop:=
 par0: par 0 | parS : forall n:nat, par n -> par (S (S n)).

(* "par" é um predicado sobre os naturais, 
definido indutivamente através de duas regras/construtores, 
que podem ser pensadas da seguinte forma:
                           par(n)
    --------- par0       ---------- parS
      par(0)               par(n+2)                      *)

Check par (S (S 0)).
Check par (S (S (S 0))).


(* A prova abaixo de que "2 é par" replica a construçao "bottom-up" de uma derivação, 
pensando nos construtores como regras, tal como indicado anteriormente.*)
Lemma par_2 : par (S (S 0)).
Proof.
apply parS.
apply par0.
Qed.

Lemma nao_par_3 : ~ par 3.
Proof.
intro H. 

inversion H. 
(*A tática "inversion" aplica-se a uma hipótese 
relativa a uma proposição definida indutivamente,
gerando um goal por cada um dos construtores/regras 
que permitam obter uma tal hipótese, acrescentando 
em cada caso as hipóteses necessárias à aplicação 
do respetivo construtor.*)

inversion H1.
(*Note-se que no caso da proposição "par 1" não há
qualquer construtor aplicável -o que corresponde a 
"uma hipótese contraditória"-, não sendo  gerado 
qualquer novo goal e ficando a prova concluída.*) 

Qed.

(*Abaixo define-se recursivamente uma função designada "e_par", 
de "nat" em "Bool", que devolve "true" exatamente quando o argumento 
é par, tal como provaremos a finalizar esta secção.*)

Fixpoint e_par (n: nat) {struct n} : Bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S p) => e_par p 
  end.


Lemma prop_e_par : forall n:nat, (e_par n = false <-> e_par (S n) = true)/\
(e_par n = true <-> e_par (S n) = false).
Proof. 
induction n.
(*A tentativa de provar cada uma das componentes desta 
conjunção, em separado, levanta dificuldades no caso indutivo.*)

(*Admitted.*)

(*caso 0*)
split.

(*1ª equivalência*)
split; intro H; compute in H; inversion H.

(*2ª equivalência*)
split; intro H;compute;reflexivity.

(*caso S n*)
destruct IHn.

split.

(*1ª equivalência*)
split. 
intro. 
apply H0 in H1. 
(*A tática "apply" também poderá actuar sobre hipóteses. 
Nesta caso, a hipótese "H1" é substituida pela 
forma equivalente que pode ser obtida do 
hipótese "H0".*)

compute. 
fold e_par.  
trivial.

intro. 
compute in H1. 
fold e_par in H1. 
apply H0. 
assumption.

(*2ª equivalência*)
split.
intro;compute;apply H;trivial.
intro H1;compute in H1;apply H;trivial.
Qed.

(*Princípio de indução associado ao predicado "par"*)
Print par_ind.


Lemma par_implica_e_par:
forall n:nat, par n -> e_par n=true.
Proof.
(*prova por indução em n levanta dificuldades; experimente; 
alternativamente, a prova seguirá por indução no predicado "par".*)

intros.

induction H.

reflexivity.

compute.
fold e_par.
assumption.
Qed.

Lemma e_par_implica_par: forall n:nat,
((e_par n=true) -> par n) /\ 
((e_par n=false) -> par (S n)).
Proof.
induction n.

(*Admitted.*)

split.
intro. apply par0.
intro H. compute in H. discriminate.
destruct IHn.
split;intro.

Search e_par.
(*O comando "Search" permite visualizar na janela de mensagens informações
acerca de um dado identificador - não alterando o estado da prova.*)
 
apply prop_e_par in H1.
(*De novo, a tática "apply" é usada do lado das hipóteses,
substituindo a hipótese "H1" pela forma equivalente 
que pode ser obtida do lema "prop_e_par".*)

compute in H1; fold e_par in H1.
apply H0;trivial.
apply parS.
apply H.
Search e_par.
apply prop_e_par;trivial.
Qed.



Theorem e_par_sse_par : forall n:nat,
e_par n=true <-> par n.
Proof.
intro.
split.
apply e_par_implica_par.
apply par_implica_e_par.
Qed.

(*O teorema anterior permite agora provar a 
paridade de um natural, com recurso a computação 
com a função "e_par". De facto, "e_par" constitui um 
"método de decisão" para o predicado "par".*)

Lemma par_100: par 100.
Proof.
apply e_par_sse_par.
compute.
reflexivity.
Qed.

Lemma nao_par_1001: ~par 1001.
Proof.
intro H.

assert(H1: e_par 1001=false).
compute;reflexivity.

apply e_par_sse_par in H.
rewrite H in H1.
discriminate.
Qed.

End Predicados_indutivos.
(**************************************************)
