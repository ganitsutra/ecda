# ecda
This is coq formalization for efficient countinos auction. 
Before you compile, you need to download following dependencies:
1. Files associated with Continous double auction projract (old implemenation using lists):
There files can be downloaded from https://github.com/suneel-sarswat/cda. Please see this link for more details. You also need to compile these files before you compile the files for this project. Make sure all the files (including files for this project) are in the same folder.
2. Equation Module:
We have used Coq's Equations Module, which is convinient way to write structural recursive functions in Coq. See https://github.com/mattam82/Coq-Equations for more details and installation options. You can install this module using following simple steps:

 a. Run 'opam repo add coq-released https://coq.inria.fr/opam/released'
 
 b. Run 'opam install coq-equations'


The file 'ecda.sh' contains all the command to compile the program; run the command 'sh ecda.sh' on the terminal to compile the files.

The main formalization is divided in the following three files.

0. NSS2021_lib.v, Definitions.v, Properties.v, MaxMatch.v, UniqueMatch.v, Programs.v : contains a publically available library from an earlier on which this project is built up. You need all these files, as stated above, to run current project. 

1. RBT.v : contains properties and other related terms and facts for RedBlack trees.
 
2. OTypes.v : Order (signature for trees) signatures for the main programs.

3. Efficient.v : contains the statements and the proofs of the main results in this work. 
