#!/bin/bash

echo 'We will run checker on two stocks.\n\n'

echo 'First compiling Extracted and Checker...\n\n'
ocamlc -c Extracted.mli 
ocamlc -o check Extracted.ml Checker.ml
echo 'Running Checker on stock 1...\n\n'
./check orderbook1 tradebook1
echo '\n----------------------------------------\n'
echo 'Running Checker on stock 2...\n\n'
./check orderbook2 tradebook2

echo '\n----------------------------------------\n'

echo '\nDeleting auxilary files...\n\n'

rm *cmo check

echo 'End of demonstration. \n\n'

