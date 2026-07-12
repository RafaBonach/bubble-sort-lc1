# A correção do algoritmo Bubble Sort

Projeto de correção formal do Bubble Sort da disciplina de Lógica Computacional 1 da Universidade de Brasília.

## Estrutura do repositório
Esse projeto foi estruturado em dois diretórios principais:

- **[/src](./src/)**: Contém o arquivo [bubble_sort.v](./src/bubble_sort.v), onde as funções e as provas foram estruturadas em Rocq/Coq.

- **[/latex](./latex/)**: Contém os arquivos necessários para gerar o relatório em PDF com LaTeX e `coqdoc`, incluindo a versão gerada do [relatório](./latex/relatorio.pdf).

Além disso, na raiz do repositório há o arquivo [bubblesort.hs](bubblesort.hs), gerado pelo mecanismo de extração do Rocq/Coq. Esse arquivo contém a versão extraída em Haskell da função formalizada; as provas são apagadas durante a extração.

## Como compilar

Como esse projeto utiliza `Makefile`, basta usar o comando `make` no terminal para compilar o código adequadamente.

Caso queira gerar um novo PDF, utilize o comando `make doc`.

Também é possível visualizar o pdf usando evince por meio do comando `make pdf`.
