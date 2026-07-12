(* begin hide *)
Require Import Arith List Lia.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.
(* end hide *)

(**
* Funcionamento de [bubble] e [bs]

A função [bubble] recebe uma lista de naturais e realiza uma única passagem de borbulhamento. Ela compara elementos consecutivos: se [x <=? y], mantém [x] antes de [y]; caso contrário, troca os dois elementos e continua a passagem.

Essa função é recursiva, mas não é estruturalmente recursiva no formato aceito diretamente por [Fixpoint]. No ramo em que ocorre troca, a chamada recursiva é feita sobre [x :: l], que não aparece como subtermo direto de [x :: y :: l]. Por isso, a formalização usa [Function] com a medida [length l] para justificar a terminação.

Uma aplicação de [bubble] não ordena necessariamente uma lista arbitrária. Por exemplo, [bubble (3 :: 2 :: 1 :: nil)] produz [2 :: 1 :: 3 :: nil]: os elementos são preservados e um elemento maior anda para a direita, mas a lista ainda não está ordenada.

A função principal [bs] ordena a cauda recursivamente e depois aplica [bubble] à lista formada pela cabeça original e pela cauda já processada. A prova de ordenação usa essa ideia: inserir um elemento no início de uma lista ordenada e aplicar uma passagem de [bubble] devolve uma lista ordenada.
*)

(* begin hide *)
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

Eval compute in bubble (2::1::nil).
Eval compute in bubble (3::2::1::nil).

Fixpoint bs (l: list nat) :=
  match l with
  | nil => nil
  | h::l' => bubble (h::(bs l'))
  end.
Eval compute in (bs (1::2::nil)).
Eval compute in (bs (2 :: 1::nil)).
Eval compute in (bs (3 :: 2 :: 1::nil)).
(* end hide *)

(** * Prova de preservação dos elementos/permutação *)

(** ** Permutação produzida por [bubble] ([bubble_perm]) *)

(** O lema [bubble_perm] afirma que uma passagem de [bubble] gera uma permutação da lista original. Ele é necessário porque [bs] usa [bubble] em cada passo; portanto, antes de provar que a lista final está ordenada, precisamos saber que uma passagem de borbulhamento não perde nem cria elementos. *)

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

(** A prova segue a própria definição recursiva de [bubble], usando
[functional induction]. Essa indução gera quatro casos.

No caso da lista vazia, [bubble nil] é [nil]. No caso de uma lista com um
elemento, [bubble (x :: nil)] também devolve [x :: nil]. Esses dois casos
são fechados por reflexividade da permutação, pois a função não altera a
lista.

Quando a lista tem pelo menos dois elementos, a prova acompanha a comparação
[x <=? y]. Se a comparação é verdadeira, [bubble] mantém [x] na cabeça e
continua sobre [y :: l0]. A hipótese de indução informa que [y :: l0] é uma
permutação de [bubble (y :: l0)]. Como a cabeça [x] não muda, [perm_skip]
leva essa permutação para as listas completas.

No ramo em que [x <=? y] é falso, a função troca os dois primeiros elementos
e passa a calcular [bubble (x :: l0)]. A lista intermediária usada na prova é
[y :: x :: l0]. Primeiro, [perm_swap] mostra que [x :: y :: l0] é permutação
de [y :: x :: l0]. Depois, [perm_skip] usa a hipótese de indução para mostrar
que [y :: x :: l0] é permutação de [y :: bubble (x :: l0)]. Por fim,
[perm_trans] junta a troca inicial com a permutação obtida na chamada
recursiva. *)

(** ** Preservação dos elementos em [bs] ([bs_perm]) *)

(** O lema [bs_perm] leva a preservação de elementos para a função completa [bs]. *)

Lemma bs_perm: forall l, Permutation l (bs l).
Proof.
  induction l as [ | h tl].
  - simpl. apply Permutation_refl.
  - simpl. apply perm_trans with (h::(bs tl)). 
    + simpl. apply perm_skip. apply IHtl.
    + simpl. apply bubble_perm.
Qed.

(** A prova de [bs_perm] é por indução estrutural na lista [l]. No caso base
[l = nil], a definição de [bs] também retorna [nil], então a permutação é
imediata.

No passo indutivo, a lista tem a forma [h :: tl]. A hipótese de indução diz
que [tl] é permutação de [bs tl]. Aplicando [perm_skip], obtemos a primeira
etapa da prova: [h :: tl] é permutação de [h :: bs tl], pois a cabeça [h] é
preservada.

A segunda etapa usa [bubble_perm]. Como [bs (h :: tl)] se reduz a
[bubble (h :: bs tl)], esse lema relaciona [h :: bs tl] com
[bubble (h :: bs tl)]. A regra [perm_trans] junta as duas etapas:
primeiro substituímos a cauda por sua versão ordenada por [bs], depois usamos
que a passagem de [bubble] não altera o multiconjunto de elementos. *)

(** * Prova de ordenação *)

(** Para a parte de ordenação usamos [Sorted le]. A relação central é [le],
isto é, menor ou igual. Na definição utilizada pela biblioteca, [HdRel le h tl]
relaciona a cabeça [h] com o primeiro elemento da cauda [tl], quando ela não é
vazia. Essa separação entre a cauda estar ordenada e a cabeça respeitar o
primeiro elemento aparece várias vezes nas provas abaixo. *)

(** ** Preservação da ordenação por [bubble] ([bubble_stability]) *)

(** O lema [bubble_stability] mostra que uma lista já ordenada é um ponto fixo de [bubble]. O nome do lema não deve ser lido como estabilidade no sentido tradicional de algoritmos de ordenação; aqui ele afirma apenas que uma passagem de [bubble] não modifica uma lista que já satisfaz [Sorted le]. *)

Lemma bubble_stability: forall l, Sorted le l -> bubble l = l.
Proof.
  intro l. functional induction (bubble l).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. intro H. inversion H; subst. rewrite IHl0.
    + reflexivity.
    + assumption.
  - simpl. apply Nat.leb_gt in e0. intro hSorted. inversion hSorted; subst. inversion H2; subst. lia.
Qed.

(** A prova usa [functional induction] sobre [bubble]. Assim como em
[bubble_perm], aparecem os casos de lista vazia, lista unitária e listas com
pelo menos dois elementos. Nos dois primeiros casos, [bubble] devolve a própria
lista, então a igualdade é direta.

No ramo em que [x <=? y = true], a função retorna
[x :: bubble (y :: l0)]. A hipótese [Sorted le (x :: y :: l0)] é invertida:
dela obtemos que a cauda [y :: l0] também está ordenada. Essa é exatamente a
informação necessária para aplicar a hipótese de indução, que reescreve
[bubble (y :: l0)] como [y :: l0]. Depois dessa reescrita, os dois lados da
igualdade ficam iguais.

No ramo em que [x <=? y = false], a comparação booleana é convertida em
[x > y]. Esse caso só aparece na indução porque [bubble] precisa considerar
todas as listas; ele é impossível sob a hipótese de que a entrada está
ordenada. Ao inverter [Sorted le (x :: y :: l0)], obtemos a relação [x <= y].
Essa relação contradiz [x > y], e a parte aritmética é fechada com [lia]. *)

(** ** Inserção da cabeça em uma cauda ordenada ([bubble_one]) *)

(** O lema [bubble_one] é o passo principal da ordenação: se a cauda [l] já está ordenada, então [bubble (x :: l)] também fica ordenada. *)

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

(** A prova de [bubble_one] é a mais trabalhosa, porque ela mostra como uma
passagem de [bubble] insere [x] em uma cauda que já está ordenada. A indução é
estrutural sobre a lista [l], que é a cauda recebida junto com [x].

Caso base. Quando [l = nil], [bubble (x :: nil)] resulta na lista unitária
[x :: nil]. Para construir a prova de ordenação, usamos [Sorted_cons]: a cauda
é ordenada por [Sorted_nil], e a relação entre a cabeça e a cauda vazia é dada
por [HdRel_nil].

Passo indutivo. Quando a cauda tem a forma [h :: tl], assumimos que ela está
ordenada. A prova abre a equação de [bubble (x :: h :: tl)] e separa os casos
da comparação [x <=? h].

Se [x <=? h = true], não ocorre troca entre [x] e [h]. O resultado tem a forma
[x :: bubble (h :: tl)]. Pela hipótese da prova, [h :: tl] já está ordenada.
Com [bubble_stability], podemos reescrever [bubble (h :: tl)] como
[h :: tl]. A comparação booleana fornece [x <= h], que é exatamente a relação
necessária para colocar [x] antes de [h]. Assim, a lista resultante permanece
ordenada.

Se [x <=? h = false], ocorre a troca inicial, e o resultado começa com [h].
Isso não é uma contradição: a comparação é convertida em [x > h], de onde a
prova usa a relação [h <= x] para manter [h] na cabeça. A partir daí, a prova
precisa observar a forma de [tl].

Quando [tl = nil], a parte recursiva é [bubble (x :: nil)], ou seja, uma lista
unitária. A ordenação de [h :: x :: nil] é construída com [Sorted_cons],
usando que a lista unitária é ordenada e que [h <= x].

Quando [tl = n :: l], a prova abre uma nova comparação, agora entre [x] e
[n]. No ramo [x <=? n = true], a chamada recursiva mantém [x] antes de [n];
a hipótese de indução trata a ordenação dessa parte recursiva, e [h <= x]
fornece a relação da cabeça [h] com o primeiro elemento da cauda resultante.

No ramo [x <=? n = false], [x] também passa por [n], e a chamada recursiva é
tratada novamente pela hipótese de indução. A diferença é que agora o primeiro
elemento depois de [h] é [n]. Como a lista original [h :: n :: l] estava
ordenada, a inversão dessa hipótese fornece a relação necessária [h <= n].
Com isso, [Sorted_cons] fecha a ordenação mantendo [h] na cabeça. *)

(** ** Ordenação produzida por [bs] ([bs_sorted]) *)

(** O lema [bs_sorted] usa [bubble_one] para provar que [bs] sempre retorna uma lista ordenada. *)

Lemma bs_sorted: forall l, Sorted le (bs l).
Proof.
  induction l as [ | h tl].
  - simpl. apply Sorted_nil.
  - simpl. apply bubble_one. apply IHtl.
Qed.

(** A prova de [bs_sorted] é por indução estrutural na lista. No caso base,
[bs nil] é [nil], e a lista vazia é ordenada por [Sorted_nil].

No passo indutivo, a lista é [h :: tl]. Pela definição da função,
[bs (h :: tl)] é [bubble (h :: bs tl)]. A hipótese de indução garante que
[bs tl] está ordenada. Portanto podemos aplicar [bubble_one] com [x = h] e
[l = bs tl]. O lema conclui exatamente que [bubble (h :: bs tl)] está
ordenada, que é o resultado de [bs] nesse caso. *)

(** ** Correção final do algoritmo ([bs_correto]) *)
(** O teorema [bs_correto] junta as duas propriedades necessárias para a correção: ordenação e preservação dos elementos. *)
    
Theorem bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l).
Proof.
  intro. split.
  - apply bs_sorted.
  - apply bs_perm.
Qed.

(** Essa prova não precisa de indução nova. O objetivo é uma conjunção:
mostrar que a saída está ordenada e que preserva os elementos da entrada.
Usamos [split] para separar as duas partes. A primeira é resolvida por
[bs_sorted], e a segunda por [bs_perm]. Juntas, essas propriedades mostram que
[bs] retorna uma lista ordenada por [le] e com os mesmos elementos da lista
original. *)


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
