# A correção do algoritmo Bubble Sort
Projeto de correção do Bubble Sort da disciplina de Lógica Computacional 1, Universidade de Brasília

## Estrutura do repositório
Esse projeto foi estruturado em dois diretórios principais:

- **[/src](./src/)**: Contem o arquivo [bubble_cort.v](./src/bubble_sort.v), onde as provas foram estruturadas em coq.

- **[/latex](./latex/)**: Contem os arquivos necessário para criar um pdf utilizando latex e também possui o arquivo do [relatório](./latex/relatorio.pdf).

Ademais, na raíz do repositório tem o arquivo [bubblesort.hs](bubblesort.hs) que contém as provas do bubble sort em haskell.

## Como compilar.
Como esse projeto está utilizando makefile, basta usar o comando `make` no terminal para que ele compile o código adequadamento.

Caso queria gerar um novo pdf, basta utilizar o comando `make doc` para gerar um novo pdf.

Também é possível visualizar o pdf usando evince por meio do comando `make pdf`.