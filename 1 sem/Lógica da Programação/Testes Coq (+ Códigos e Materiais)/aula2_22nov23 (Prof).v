(*Aula 22/11/2023*)

(*Exemplificações relativas às Lógicas de Primeira Ordem Intuicionista e Clássica.*)

Section Calculo_Predicados.

Variable D:Set.
(*"Set" é uma das "sorts" do Coq (à semelhança de "Prop" - uma sort é um "tipo de tipos"),
correspondendo a uma certa coleção de conjuntos/tipos, que inclui,
por exemplo, "nat" um tipo indutivo que representa os 
números naturais. "D" será então um conjunto abstrato desta coleção,
que podemos associar ao domínio de uma estrutura abstrata para 
um tipo de linguagem de primeira ordem.*)
 
Check Set.
Check nat.

(*O conjunto de declarações que se segue pode ser visto como 
a declaração de um tipo de linguagem de primeira ordem com: 
-uma constante "c"; 
-um símbolo de função unário "f"; 
-um símbolo de função binário "g";
-símbolos de relação unários "P" e "Q"; 
-um símbolo de relação binário "R".*)

(*Declaração dos símbolos de função.*)

Variable c: D.
Variable f: D->D.
Variable g: D->D->D.

Check f c.
Check g c (f c).
Check g c.
(*Apesar de não ser uma expressão de tipo "D", "g c" 
é uma expressão tipificável em Coq, com tipo "D->D".*)

(*Declaração dos símbolos de relação.*)

Variables P Q: D->Prop.
Variables R: D->D->Prop.

Check P (f c).
Check R (f c) (f c).
Check R (f c).
(*De novo, apesar de não ter tipo "Prop", 
a expressão "R (f c) "é tipificável em Coq, com tipo "D->Prop" 
- o tipo dos predicados unários sobre "D".*)

(*Notação Coq para as duas formas de quantificação.*)

Check forall x:D, P x.
(*O Coq dispensa a identificação do domínio da quantificação, 
caso o consiga reconstruir.*)

Check forall x, P x.
Check exists x y, R x y.

(*******************************************)
(*Alguns teoremas sobre a sintaxe definida.*)
(*******************************************)



(*Aplicação de hipóteses quantificadas universalmente.*)

Lemma hip_univ_1: (forall x, R x x)-> R c c.
Proof.
intro H.

specialize H with c.
(*A tática "specialize" permite particularizar uma 
hipótese quantificada universalmente ("H" no caso), substituindo 
a respetiva variável ("x" no caso) por um termo ("c" no caso), 
adicionando-a ao contexto de hipóteses, o que corresponde 
a uma inferência de eliminação da quantificação universal.*) 

assumption.
Qed.

Lemma hip_univ_2: (forall x y, R x y)-> R (f c) c.
Proof.
intro.

specialize H with (f c) c.
(*No caso de quantificações múltiplas, torna-se necessário
fornecer tantos termos quantas as variáveis quantificadas.*)
 
assumption.
Qed.

Lemma hip_univ_3: (forall x y, R x y)-> R (f c) c.
Proof.
intro H.

apply H.
(*A tática "apply" procura automaticamente fazer o "matching" 
da hipótese indicada (no caso "H") com o atual goal, 
gerando eventualmente novos subgoals (no caso não há novos subgoals).*) 

Qed.

Lemma hip_univ_4: ((forall x, P x->R x x)/\ P c)-> R c c.
Proof.
intros.
destruct H as [H1 H2].

apply H1.
(*Neste caso, a tática "apply" gerou como novo subgoal "P c".*)

assumption.
Qed.

(*Algumas equivalências envolvendo quantificações e 
conetivos proposicionais.*)

Lemma exist_distrib_disj: (exists x, (P x \/ Q x))<-> 
(exists x, P x)\/(exists x, Q x).
Proof.
split;intro.

(*=>*)
destruct H.

(*Neste caso, a tática "destruct" tem um efeito 
semelhante a uma inferência de eliminação da quantificação existencial, 
com a hipótese "H" como premissa principal. A condição
lateral, necessária à correta aplicação desta regra,
fica acautelada com a utilização de uma variável (no caso "x") 
que não tem ocorrências livres nem na goal, nem nas hipóteses.
Em Coq, também a quantificação existencial é definida como um tipo indutivo
(tal como a disjunção, a conjunção e o absurdo). A tática 
"elim" também poderia ser aplicada à hipótese existencial 
"H" -seguida de "intros", obtendo-se um efeito semelhante.*)

destruct H.
left.

exists x.
(*A tática "exists" realiza uma inferência de introdução
da quantificação existencial, recorrendo ao termo passado 
como argumento (no caso "x") para a substituição da 
variável quantificada.*)

assumption.
right;exists x;assumption.

(*<=*)

destruct H as [H1|H2].
(*Num "destruct" sobre uma disjunção, é possível indicar
o nome para a nova hipótese em cada um dos casos.*)

destruct H1 as [y H3].
(*Num "destruct" sobre uma quantificação existencial, é 
possível indicar o nome (no caso "y") para um objeto 
que se assumirá satisfazer a proposição em questão (no caso "P x \/ Q x"), 
assim como o nome (no caso "H3") para a hipótese de que, de facto,
esse objeto satisfaz a referida proposição 
(designadamente "P y \/ Q y").*)

exists y;left;assumption.
destruct H2 as [y H3].
exists y;right;assumption.
Qed.

Lemma univ_distrib_conj: (forall x, (P x /\Q x))<-> 
(forall x, P x)/\(forall x, Q x).
Proof.
split;intro.

(*=>*)
split.

intro.
(*Neste caso, a tática "intro" corresponde a uma inferência 
de introdução da quantificação universal. A condição lateral, 
necessária à correta aplicação desta regra, é acautelada com 
a geração de um nome novo (sem ocorrências livres nas hipóteses.*)

specialize H with x.
destruct H; assumption.


intro.
apply H.
(*Note-se que a tática "apply" também procura o matching 
 da goal em componentes de conjunções.*)

(*<=*)
intro; split.
destruct H.
apply H.

apply H.
(*De novo, note-se o matching da goal com 
uma componente de uma conjunção.*)

Qed.

Lemma neg_exist_equivalente_univ_neg: ~(exists x:D, P x)<-> 
forall x:D, ~P x.
Proof.
split;intros.

(*=>*)
intro.
apply H.
exists x; assumption. 

(*<=*)
intro H1;destruct H1.

(* apply H. *)
(*Neste caso, a tática "apply", por si, não consegue realizar
 o match da goal com a hipótese "H".*)

(*No entanto, é possível ajudar o Coq nesta tarefa, fornecendo um termo 
(no caso "x") para a especialização da hipótese.*)
apply H with x.


assumption.
Qed.

(*A implicação que se segue é válida intuicionisticamente, 
mas a sua recíproca não (apesar de ser válida classicamente).*)

Lemma exist_neg_implica_neg_univ: (exists x:D, ~P x)-> 
~forall x:D, P x.
Proof.
intros H1 H2.
destruct H1 as [x H3]; apply H3; apply H2.
Qed.

(*Justifiquemos a implicação recíproca em lógica clássica.*)

Require Import Classical.

(*Recordemos um dos princípios caracterizadores da lógica clássica,
nomeadamente a "lei da dupla negação", disponível na biblioteca Coq 
relativa a Lógica Clássica, com a designação
"NNPP" (e tipo "forall p : Prop, ~ ~ p -> p")*)  

Check NNPP.


Lemma neg_univ_implica_exist_neg: ~(forall x:D, P x) 
->(exists x:D, ~P x).
Proof.
intro H.
apply NNPP.
(*Note-se a aplicação da lei da dupla negação.*)

intro H1.
apply H.
intro x.
apply NNPP.
(*Nova aplicação da lei da dupla negação.*)

intro H2.
apply H1.
exists x; assumption.
Qed.

(*O seguinte princípio, válido em lógica de primeira ordem clássica, 
requer múltliplas aplicações da lei da dupla negação. Este princípio 
foi popularizado como "Drinker's Paradox", motivado pela interpretação
das quantificações na fórmula sobre o conjunto das pessoas num pub 
e "P x" como "x bebe".  
*)

Lemma drinker_paradox: exists x, (P x -> forall x, P x).
Proof.
apply NNPP.
intro H.

assert (H1: forall x, (P x /\exists x0 : D, ~ P x0)).
(*Recorde-se que a tática "assert" permite "afirmar" uma dada proposição/lema, 
acrescentando-a como hipótese (no caso com o nome "H1") e 
simultaneamente como uma nova goal a provar. 
Este lema é motivado pela consideração 
de equivalências familiares em lógica clássica, que iremos 
implicitamente justificar adiante, na prova do lema. *)

(* Na presença de várias goals a provar, a tática "n:{" permite 
indicar que começaremos por focar na "n"-ésima goal. Comecemos por focar 
no nosso goal inicial, mas agora no contexto enriquecido com a
hipótese/lema "H1" que acabámos de afirmar. *) 

2:{

assert (H2:exists x0 : D, ~ P x0).

specialize H1 with c.
(*Note-se que este raciocíno tira partido da presença da declaração 
"c:D" no contexto, o que, em termos semânticos pressupõe o "domínio D" 
não vazio.*)

destruct H1;assumption.
destruct H2 as [x0 H3].
apply H3.
apply H1.

}
(*A tática "}" assinala que terminamos a prova da goal 
em que haviamos focado, permitindo focar numa outra goal.
Neste caso, há apenas um goal adicional a provar, relativo 
ao lema H1 que afirmámos anteriormente.
*)


intro x.
split.

(*prova do lado esquerdo da conjunção*)

apply NNPP.
intro H1.
apply H.
exists x.
intro. 
(*Note-se que as hipóteses "H0" e "H1" são contraditórias.*)
contradiction.


(*prova do lado direito da conjunção*)

apply NNPP.
intro H1.
apply H.
exists x.
intro.
intro x0.
apply NNPP.
intro H2.
apply H1.
exists x0.
assumption.

(*Note-se que na prova do lema "H1" afirmado, foi essencial 
tirar partido da hipótese inicial "H" duas vezes, de forma muito distinta, 
em cada um dos subgoals induzido pela conjunção.*)

Qed.

End Calculo_Predicados.


