(* begin hide *)
Require Import Arith List Lia.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.
(* end hide*)

(**
Este trabalho apresenta uma prova formal da correção do algoritmo de ordenação por borbulhamento (a função [bs] a seguir). A formalização foi feita no assistente de provas Coq. O assistente de provas Coq utiliza o sistema de Dedução Natural, o que o torna adequado para o desenvolvimento de atividades computacionais no curso de Lógica Computacional 1. O Coq permite a extração de código certificado em diversas linguagens funcionais, como Ocaml, Haskell e Scheme. *)

(** Iniciaremos definindo a função [bubble] que recebe uma lista de naturais como argumento, e percorre esta lista comparando elementos consecutivos. Chamamos este processo de borbulhamento: *)

Function bubble (l: list nat ) {measure length l} :=
  match l with
  | nil => nil
  | x::nil => x::nil
  | x::y::l =>
      if x <=? y
      then x::(bubble (y::l))
            else y::(bubble (x::l))
            end.
Proof.
  - auto.
  - auto.
Defined.

(** Observe que esta função não é estruturalmente recursiva porque, por exemplo, a lista [(x::l)] não é uma sublista da lista original [(x::y::l)]. Neste caso, utilizamos [Function] para construir esta função e precisamos fornecer a medida que decresce em cada chamada recursiva, além de provar que esta medida efetivamente decresce a cada chamada recursiva. Por exemplo, [bubble (2::1::nil)] retorna a lista [(1::2::nil)].

 *)

Eval compute in bubble (2::1::nil).

(**

<<
   = 1 :: 2 :: nil
     : list nat
>>

*)

(** Entretanto, consequimos observar a não recursividade da função [bubble] a seguir. Em um exemplo onde a lista é [(3::2::1::nil)], a função retorta como resultado [(2::1::3::nil)], que apesar de ser uma permutação da lista original, ela não é o resultado ordenado da lista. *)

Eval compute in bubble (3::2::1::nil).

(**

<<
    = 2 :: 1 :: 3 :: nil
     : list nat
>>

*)

(** A função principal, ou seja, o algoritmo bubble sort propriamente dito, é dada pela função [bs] abaixo que recebe uma lista de naturais como argumento:

*)

Fixpoint bs (l: list nat) :=
  match l with
  | nil => nil
  | h::l' => bubble (h::(bs l'))
  end.           
(* begin hide *)
Eval compute in (bs (1::2::nil)).
Eval compute in (bs (2 :: 1::nil)).
Eval compute in (bs (3 :: 2 :: 1::nil)).
(* end hide *)

(** Neste caso sim, a função [bs] deve ser capaz de ordenar a lista orignal. Entretando, precisamos realizar algumas provas para garantir que de fato, bs seja capaz de causar a ordenação de uma lista. *)


(** * Métodos de prova*)

(** ** Definições *)
(** Antes de mais nada, podemos trazer algumas definições que nos ajudaram a provar que uma lista foi ordenada após ela ter passado pelo algoritmo de borbulhamento [bs]*)

(** H.I. 1: O predicado [Permutation] será nossa segunda hipotese de indução que definiremos para ajudar a provar o nosso algoritmo. *)

Inductive Perm : list nat -> list nat -> Prop :=
  | perm_refl : forall l, Perm l l
  | perm_trans : forall (l1 l2 l3: list nat), Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3
  | perm_const : forall (x: nat) (l1 l2: list nat), Perm l1 l2 -> Perm (x::l1) (x::l2)
  | perm_swap : forall (x y: nat) (l: list nat), Perm (x::y::l) (y::x::l).

  (** No caso dessa hipotese, ela provará que nosso algoritmo gerou uma permutação da lista original provando:
  - [perm_refl]: Uma lista é permutação de si mesma.
  - [perm_trans]: Se uma lista é permutação de outra, e esta é permutação de uma terceira, então a primeira é permutação da terceira.
  - [perm_const]: Se uma lista é permutação de outra, então adicionar um elemento no início a ambas resulta em listas que são permutações uma da outra.
  - [perm_swap]: Se dois elementos adjacentes são trocados, as listas resultantes são permutações uma da outra. *)

(** Finalmente, conseguimos definir um teorema que nos permite concluir que duas listas com os mesmos elementos e mesma quantidade de elementos são permutações uma da outra: *)

Theorem perm_eq: forall (l1 l2: list nat), (forall x, count_occ Nat.eq_dec l1 x = count_occ Nat.eq_dec l2 x) -> length l1 = length l2 -> Perm l1 l2.
Proof.
  Admitted.

(** ** Provando permutação *)
(** Com algumas definições estabelecidas, podemos começar a provar a corretude do algoritmo de ordenação por borbulhamento [bs].*)

(** *** Lema 1: Permutação da lista ordenada -> Lista original*)

(** A lista gerada pelo algoritmo de ordenação [bs] é uma permutação da lista original
nesse primeiro lema, queremos provar que ao passar qualquer lista de n elementos naturais pelo algoritmo de ordenação, o mesmo deve retornar uma permutação da lista original: *)

Lemma perm_bs: forall l, Perm (bubble l) l.
Proof. 
  intro l. functional induction (bubble l). 
  - simpl. apply perm_refl.
  - simpl. apply perm_refl.
  - simpl. apply perm_const. apply IHl0.
  - simpl. apply perm_trans with (y::x::l0). 
    + apply perm_const. apply IHl0. 
    + apply perm_swap. 
Qed.

(** Inicialmente, definimo a lista l e o que queremos provar. Em seguida, provamos os casos base:
- perm nil -> nil 
- perm (x :: nil) -> (x :: nil) 

Então, finalmente provamos a permutação perm (x :: y :: l0) -> (x :: y :: l0). Para isso, usamos a regra [perm_const] para obtermos Perm (bubble (y :: l0)) - > (y :: l0).
Como a nossa hipose [IHl0] é equivalente ao que quremos provar, conseguimos aplica-la.

Em seguida, precisamos provar mais uma das folhas de objetivos:
- perm (y :: bubble (x :: l0)) -> (x :: y :: l0).

Para conseguirmos provar essa ramificação utilizamos o predicado [perm_trans], que fará uma permutação entre os dois elementos em uma lista.

Assim, obteremos Perm (y :: bubble (x :: l0)) -> (y :: x :: l0) possibilitando que seja provado da mesma forma que a ramificação anterior, utilizando o predicado [perm_const] e a hipotese [IHl0].

Finalmente, basta aplicar [perm_swap] no sequente Perm (y :: x :: l0) -> (x :: y :: l0) que a prova é finalizada. *)


(** *** Lema 2: *)
(** Agora, vamos provar que a função recursiva [bs] retorna uma permutação da lista original através do seguinte lema: *)

Lemma bs_permuta: forall l, Perm (bs l) l.
Proof.
  induction l as [ | h tl].
  - simpl. apply perm_refl.
  - simpl. apply perm_trans with (h::(bs tl)).
    + simpl. apply perm_bs.
    + simpl. apply perm_const. apply IHtl.
Qed.

(** Para realizar essa prova, estabelecemos que uma lista l é estruturada por uma cabeça h e um corpo tl.
A partir daí, provamos trivialmente que para uma lista vazia, o [bs] retorna uma permutação de uma lista vazia.

Em seguida, precisamos provar que a função [bs] retorna uma permutação da lista original, ou seja, Perm (bubble (h :: bs tl)) |- (h :: tl).

Para isso, usamos a regra [perm_trans] com a lista (h :: (bs tl)). Isso divide a nossa prova em duas partes:
- 1º Perm (bubble (h :: bs tl)) |- (h :: (bs tl)) que é provado pelo lema 1, ou seja, [perm_bs].
- 2º Perm (h :: (bs tl)) |- (h :: tl): Para provar essa ramificação, precisamos:
  - utilizar a regra [perm_const] para retira a constante h da lista, já que ela já está na posição que deveria estar;
  - aplicamos a hipótese de indução [IHtl] provando assim que a lista tl é uma permutação da lista bs tl.
*)

(** ** Provando Ordenação *)
(** Agora que provamos que o algoritmo bubblesort consegue retornar uma permutação da lista original,
precisamos provar que o algoritmo é capaz de ordenar a lista. *)

(** *** Lema 3: *)
(** Primeiro, precisamos provar que, para uma lista ordenada, a função [bubble] é capaz de mante-la ordenada. Para isso, utilizaremos o lema a seguir: *)

Lemma bubble_sorted: forall l, Sorted le l -> bubble l = l.
Proof.
  intro l. functional induction (bubble l).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. intro H. inversion H; subst.
    + rewrite IHl0.
      * reflexivity.
      * assumption.
  - simpl. apply Nat.leb_gt in e0. intro hSorted.
    + inversion hSorted; subst. inversion H2; subst. lia.
Qed.

(** Essa prova é realizada por indução sobre a função bubble, fazendo com que a demonstração seja dividida em quatro casos.

- 1º - Lista vazio ([nil]):

  Essa prova é trivial pois a função [bubble] retorna a lista vazia, que é igual a lista vazia.


- 2º - Possui 1 elemento ([x :: nil]):

  Também é trivial, pois se a função [bubble] receber uma lista com um único elemento, ela retorna essa mesma lista, que é equivalente a lista ordenada.


- 3º - Possui pelo menos 2 elementos ([x :: y :: l0], [x <= y]):

  Nesse caso, a lista não realizará a troca entre os dois elementos e processegue recursivamente para a sublista y :: l0, assim temos que temos que  x :: bubble (y :: l0) = x :: y :: l0.
  Como a lista permace ordenada, tomamos por hipotese de indução bubble (y :: l0) = y :: l0. Assim, aplicando a h.i., temos que x :: y :: l0 = x :: y :: l0, que é verdade.
  
  Com isso, provamos que para uma lista ordenada, a função [bubble] retorna a mesma lista ordenada.
  

- 4º - Possui pelo menos 2 elementos ([x :: y :: l0], [x > y]):

  Esse é um caso particular, pois a forma que o nosso lema foi estruturado torna o caso impossível de ser provado assumindo que a lista recebida por [bubble] esteja ordenada.
  Inicialmente, tema a premisa (x <=? y) = false, ou seja, x > y. Assim, a função [bubble] retornará y :: bubble (x :: l0).
  Entretanto, o passo indutívo consiste em provar Sorted le (x :: y :: l0) -> y :: bubble (x :: l0) = x :: y :: l0. Desta forma, utilizando a nossa premissa booleana,
  chegamos a uma contradição, invalidando esse caso com prova para a ordenação de uma lista ordenada utilizando o algoritmo [bubble].
*)

(** *** Lema 4: *)

Lemma bs_sorted: forall l, Sorted le (bs l).
Proof. 
  intro l. functional induction (bubble l).
Admitted.

(* begin hide *)

(*
(** A seguir, mostraremos que o algoritmo bubblesort (função [bs]) gera como saída uma permutação da lista de entrada. O lema a seguir nos diz que a função [bubble] também gera uma permutação da entrada: *)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  intro l. functional induction (bubble l). Admitted.


(** Por fim, a correção do algoritmo [bs] é obtida pelo teorema a seguir que estabelece que o algoritmo [bs] retorna uma permutação da lista de entrada que está ordenada: *)
    
Theorem bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l).
Proof.
Admitted.

*)

(* end hide *)

(** Repositório: %\url{https://github.com/RafaBonach/bubble-sort-lc1.git}% *)