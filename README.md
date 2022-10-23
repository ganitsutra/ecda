# Efficient and Verified Continuous Double Auctions
This is the coq formalization accompanying our paper. 

To compile our Coq code, you need to have a Coq compiler. We have tested our code using Coq version 8.12.2, and it compiles successfully without errors.

Furthermore, before you can compile, you need to download and install the Coq's Equations Module.
See https://github.com/mattam82/Coq-Equations for more details and installation options. You can install this module using the following commands in your shell:
 a. Run 'opam repo add coq-released https://coq.inria.fr/opam/released'
 b. Run 'opam install coq-equations'

Finally, you can compile our Coq formalization using the following command in your shell.
    sh run.sh
This command will compile our Coq formalization and also extract two programs in the `../application/' folder (corresponding to the earlier List implementation and our new Red-black tree implementation).

Our new formalization consists of three main files, which we briefly describe below.

1. RBT.v : contains definitions, properties, and lemmas for Red-black trees. This extends the Coq standard library as explained in our paper.
 
2. OTypes.v : contains an instantiation of red-black trees to our application by setting the appropriate keys and types of elements of the tree.

3. Efficient.v : contains the statements and the proofs of the main results in our work. 

The other Coq files are taken from the previous formalization, which is publically available on github.com/suneel-sarswat/cda.
