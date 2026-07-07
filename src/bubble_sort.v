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

(** ** Provando permutação *)
(** Com algumas definições estabelecidas, podemos começar a provar a corretude do algoritmo de ordenação por borbulhamento [bs].*)

(** *** Lema 1 *)

(** O primeiro lema que precisamos provar é que a permutação é preservada pelo algoritmo de borbulhamento: *)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  intro l. functional induction (bubble l).
  - simpl. apply Permutation_refl.
  - simpl. apply Permutation_refl.
  - simpl. apply perm_skip. apply IHl0. 
  - simpl. apply perm_trans with (y::x::l0). 
    + apply perm_swap. 
    + simpl. apply perm_skip. apply IHl0.
Qed.

(** Para provar esse lema, será necessário provar 4 casos:
- 1. Permutação () = bubble ():
  
  Esse caso é provado trivialmente, dado que a permutação de uma lista vazia é própia lista vazia. O algoritmo [bubble] retorna uma lista vazia. 

- 2. Permutação (x :: nil) = bubble (x :: nil): 

  Esse caso é provado trivialmente, dado que a permutação de uma lista com um único elemento é própria lista. O algoritmo [bubble] retorna a lista com o único elemento.

- 3. Permutação (x :: y :: l0) = bubble (x :: y :: l0): 

  Esse caso pode ser provado utilizando uma regra de permutação [perm_skip], que diz que a permutação de uma lista com um elemento constante é equivalente a permutação da sublista. Assim, podemos aplicar a hipótese de indução [IHl0] para provar que a sublista l0 é uma permutação da lista bubble l0.

- 4. Permutação (y :: x :: l0) = bubble (y :: x :: l0): 

  Para provarmos esse caso, precisaremos utilizar a regra de permutação [perm_trans] com a lista (y :: x :: l0). Essa regra diz que se uma lista é uma permutação de outra, e essa segunda lista é uma permutação de uma terceira, então a primeira lista é uma permutação da terceira.
  Como a lista (y :: x :: l0) é uma permutação da lista (x :: y :: l0) e a lista (x :: y :: l0) é uma permutação da lista bubble (y :: x :: l0), podemos concluir que a lista (y :: x :: l0) é uma permutação da lista bubble (y :: x :: l0).
  Assim, para a primeira ramificação dessa prova, lista (y :: x :: l0) é uma permutação da lista (x :: y :: l0), podemos aplicar a regra de permutação [perm_swap] que diz que a permutação de uma lista com dois elementos é equivalente a permutação da lista com os elementos trocados de posição, concluindo essa ramificação.
  Depois, provamos a segunda ramificação, lista (x :: y :: l0) é uma permutação da lista bubble (y :: x :: l0), utilizando a regra de permutação [perm_skip] e aplicando a hipótese de indução [IHl0] para provar que a sublista l0 é uma permutação da lista bubble l0.

Assim, concluimos a prova do lema 1, que diz que a função [bubble] retorna uma permutação da lista original.
*)

(** *** Lema 2: *)
(** Agora, vamos provar que a função recursiva [bs] retorna uma permutação da lista original através do seguinte lema: *)

Lemma bs_perm: forall l, Permutation l (bs l).
Proof.
  induction l as [ | h tl].
  - simpl. apply Permutation_refl.
  - simpl. apply perm_trans with (h::(bs tl)). 
    + simpl. apply perm_skip. apply IHtl.
    + simpl. apply bubble_perm.
Qed.

(** Para provar esse lema, será necessário provar 2 casos:
- 1. Permutação () = [bs] ():
  
  Esse caso é provado trivialmente, dado que a permutação de uma lista vazia é própia lista vazia. O algoritmo [bs] retorna uma lista vazia. 

- 2. Permutação (h :: tl) = [bs] (h :: tl): 

  Para provar esse caso, precisaremos utilizar a regra de permutação [perm_trans] com a lista (h :: (bs tl)). Essa regra diz que se uma lista é uma permutação de outra, e essa segunda lista é uma permutação de uma terceira, então a primeira lista é uma permutação da terceira.
  Com isso, teremos duas ramificações a serem provadas:

  - 1º Perm (h :: tl) |- (h :: (bs tl)): Para provar essa ramificação, podemos aplicar a regra de permutação [perm_skip] que diz que a permutação de uma lista com um elemento constante é equivalente a permutação da sublista.
  Em seguida, basta usar a hipotese de indução [IHtl], permutação da sublista tl é equivalente a permutação da lista [bs] tl.

  - 2º Perm (h :: (bs tl)) |- [bs] (h :: tl): Para provar essa ramificação, basta utilizar o lema 1 [bubble_perm], que diz que a função [bubble] retorna uma permutação da lista original.

Assim, concluimos a prova do lema 2, que diz que o algoritmo recursivo [bs] retorna uma permutação da lista original.
*)

(** ** Provando Ordenação *)
(** Agora que provamos que o algoritmo bubblesort consegue retornar uma permutação da lista original,
precisamos provar que o algoritmo é capaz de ordenar a lista. *)

(** *** Lema 3: *)
(** Primeiro, precisamos provar que, para uma lista ordenada, a função [bubble] é capaz de mante-la ordenada. Para isso, utilizaremos o lema a seguir: *)

Lemma bubble_stability: forall l, Sorted le l -> bubble l = l.
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

(** Agora, precisamos provar uma caracteristica fundamental da função [bubble], que ela consegue fazer com que o maior elemento de uma lista torne-se o último elemento. Para isso, usaremos o lema a seguir: *)

Lemma bubble_one: forall x l, Sorted le l -> Sorted le (bubble (x :: l)).
Proof.
  induction l as [ | h tl].
  - simpl. intro. apply Sorted_cons. apply Sorted_nil. apply HdRel_nil.
  - simpl. intro H. rewrite bubble_equation. destruct (x<=?h) eqn:i.
    + apply Nat.leb_le in i. inversion H; subst. apply Sorted_cons. rewrite bubble_stability. auto. auto. rewrite bubble_stability. auto. assumption.
    + generalize dependent tl. intro tl. case tl.
      * intros. apply Nat.leb_gt in i. inversion H; subst. apply Sorted_cons. rewrite bubble_stability. auto. auto. rewrite bubble_equation. apply HdRel_cons. lia. 
      * intros. rewrite bubble_equation in *. destruct (x<=?n) eqn:u.
        ** apply Nat.leb_gt in i. inversion H; subst. apply Sorted_cons. apply IHtl. apply H2. apply HdRel_cons. lia.
        ** apply Nat.leb_gt in i. apply Nat.leb_gt in u. inversion H; subst. apply Sorted_cons. apply IHtl. apply H2. apply HdRel_cons. inversion H3. subst. assumption.
Qed.

(** O lema [bubble_one] é provado através de duas ramificações:
- \textbf{1° - () -> [bubble] (x :: ())}:

  Iniciamos introduzindo o primeiro termo da implicação, e então utilizamos a regra [Sorted _cons] para abrir a nossa lista ordenada em uma lista vazia, que é provada trivialmente com [Sorted_nil], e a relaçõo de um terma com o vazio, que resultantemente dá o termo. Assim provamos que para uma lista com um único termo, o teorema é válido.

- 2° - (h :: tl) -> [bubble] (x :: h :: tl):

  Iniciamos da mesma forma que o ramo anterior. Entretando, para que esse lado funcione, é necessário abrir a função [bubble] para dividir em duas novas ramificações. Essa abertura é necessária para tirarmos do [bubble] o primeiro elemento da lista. Isso divide a nossa arvore de provas em duas ramificações:

  - Sorted le (x :: bubble (h :: tl)), para (x <= h):

    Nessa ramificação, conseguimos utilizar a hipotese que h < tl que é resultante da hipotese que tl está ordenado para abrimos mais uma vezes a nossa premissa em Sorted le (bubble (h :: tl)) e x < (bubble (h :: tl)). Assim, utilizamos a nossa o lema [bubble_stability] para provar que bubble (h :: tl) = h :: tl, e então conseguimos provar que Sorted le (h :: tl).
    
    Em seguida, utilizamos novamente a regra [bubble_stability] para termos as das ramificações, x < (h :: tl), que é provado trivialmente pelas hipoteses; Sorted le (h :: tl), que também é provado trivialmente.

  - Sorted le (h :: bubble (x :: tl)), para (x > h):
  
    Para essa ramificação, precisaremos estruturar uma prova para a calda da lista [tl]. Para isso, generalizamos a nossa prova para todos os tipos de calda de lista e provamos para cada tipo de calda:

      - Caso a calda seja vazia (tl = nil):

        Nesse caso, precisamos provar que (h :: bubble (x :: nil)) está ordenado. Para isso, utilizamos a regra [Sorted_cons] para abrirmos a nossa lista ordenada e provamos que bubble (x :: nil) = x :: nil. Em seguida, usamos a função [bubble] que nos retorna h<=x, gerando assim uma contradição nessa ramificação, uma vez que temos como premissa h<x.

      - Caso a calda não seja vazia (tl = l):

        Nesse caso, teremos de entrar mais uma vez na função [bubble], criando outras duas ramificações:
          
          - (h :: x :: bubble (n :: l)), para (x <= n):

            Nessa ramificação, utilizamos a regra [Sorted_cons] para tirarmos [h] da lista, já que ele já está ordenado e então usamos a hipotese de indução para provar que (x :: bubble (n :: l)) está ordenado. Em seguida, provamos que o elemento h <= (x :: bubble (n :: l)), que gera uma contradição com a premissa que h < x.

          - (h :: n :: bubble (x :: l)), para (x > n):

            Nessa ramificação, repetimos os mesmo passos da ramificação anterior, com a diferença que agora de fato h <= (n :: bubble (x :: l)), condizendo com a nossa premissa h <= n.

Desta forma, provamos que a função [bubble] consegue fazer com que o maior elemento de uma lista torne-se o último elemento.

*)

(** *** Lema 5: *)

(** Por fim, provamos que o algoritmo [bs] ordena uma lista com o lema a seguir: *)

Lemma bs_sorted: forall l, Sorted le (bs l).
Proof.
  induction l as [ | h tl].
  - simpl. apply Sorted_nil.
  - simpl. apply bubble_one. apply IHtl.
Qed.

(** Essa prova é uma prova simples por utilizar o lema anterior [bubble_one]. Para realizar essa prova, precisamos fazer indução em l. Isso nos dá 2 casos principais para provar:|

- 1° - [bs] ordena uma lista vazia: É provado trivialmente utilizando a regra de ordenação [Sorted_nil], ou seja, uma lista vazia está ordenada.

- 2° - Ordenar 1 terma em uma lista ordenada (bubble (h :: bs tl)): Nesse caso, usamos o lema [bubble_one] para provar que o elemento maior se move para a posição correta. Isso resulta em Sorted (bs l), ou seja, o resultado de [bs] está ordenado, que é provado pela nossa Hipotese de indução [IHtl], que diz que [bs] ordena a sublista tl.

Com isso, provamos que a nossa função [bs] ordena uma lista de naturais, ou seja, a função [bs] retorna uma lista ordenada.
*)

(** ** Teorema Final *)
(** Por fim, a correção do algoritmo [bs] é obtida pelo teorema a seguir que estabelece que o algoritmo [bs] retorna uma permutação da lista de entrada que está ordenada: *)
    
Theorem bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l).
Proof.
  intro. split.
  - apply bs_sorted.
  - apply bs_perm.
Qed.

(** A prova desse teorema é bem simples. Primeiro quebramos o nosso sequente em duas ramificações:

- 1° - Provar que [bs] ordena a lista de entrada: Para isso, utilizamos o lema [bs_sorted], que diz que a função [bs] ordena uma lista de naturais.

- 2° - Provar que [bs] retorna uma permutação da lista de entrada: Para isso, utilizamos o lema [bs_perm], que diz que a função [bs] retorna uma permutação da lista original.

Assim, provamos que o algoritmo [bs] retorna uma permutação da lista de entrada que está ordenada, ou seja, o algoritmo [bs] é correto.
*)


(* begin hide *)

(** ** Extração de código *)


Require Extraction.

(** As opções de linguagens são: Ocaml, Haskell e Scheme. *)
Extraction Language Haskell.

(** Extração apenas da função [bs]. *) Extraction bs.

(** Extração do programa inteiro. *) Recursive Extraction bs.

(** Extração para um arquivo. *) Extraction "bubblesort" bs.

(* end hide *)

(** Repositório: %\url{https://github.com/RafaBonach/bubble-sort-lc1.git}% *)