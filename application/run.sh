#!/bin/bash

echo 'In this demonstration, we run our program on two order books of sizes 100,000 and 200,000.\n\n'

echo 'First compiling the old List implementation...\n\n'
ocamlc -c Extracted.mli 
ocamlc -o check_list Extracted.ml Checker_list.ml
echo 'Running the old List implementation on 100,000 instructions. This may take approximately upto one minute, depending on your system. The exact time required will be printed as soon as this task terminates. \n\n'
time ./check_list orderbook_100000
echo '\n----------------------------------------\n'
echo 'Now running the old List implementation on 200,000 instructions. This may take approximately upto four minutes, depending on your system. The exact time required will be printed as soon as this task terminates. \n\n'

time ./check_list orderbook_200000

echo '\n----------------------------------------\n'

echo '\nDeleting auxiliary files...\n\n'

rm *cmo *cmi check_list

echo '\n----------------------------------------\n'

echo 'Now compiling the new Red-black tree implementation...\n\n'
ocamlc -c Extracted_tree.mli 
ocamlc -o check_tree Extracted_tree.ml Checker_tree.ml
echo 'Running the new Red-black tree implementation on 100,000 instructions. This may take a few seconds, depending on your system. The exact time required will be printed as soon as this task terminates. \n\n'
time ./check_tree orderbook_100000
echo '\n----------------------------------------\n'
echo 'Running the new Red-black tree implementation on 200,000 instructions. This may take a few seconds, depending on your system. The exact time required will be printed as soon as this task terminates. \n\n'
time ./check_tree orderbook_200000

echo '\n----------------------------------------\n'

echo '\nDeleting auxiliary files...\n\n'

rm *cmo *cmi check_tree

echo 'End of demonstration. \n\n'

