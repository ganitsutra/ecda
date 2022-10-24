#Efficient and Verified Continuous Double Auctions

This folder consists of the demonstration accompanying our paper.

Before you can run the demonsration, make sure that you have an OCaml compiler installed by typing the following command on your terminal. 

    ocaml --version

Once you have ensured that an OCaml compiler is installed, you can run our demonstration by typing the following command on your terminal.

    sh run.sh
    
This demonstration runs the two implementations, namely the List and the Red-black tree implementations, of continuous double auctions on two randomly generated order books and records the running time of generating the verified trade books. The python script used for generating a random order book is also included as create_orderbook.py.

Note, the above demonstration uses the verified programs Extracted.ml* Extracted_tree.ml*, which are directly extracted by compiling the accompanying Coq formalization. If you wish, you may delete these programs and run the Coq formalization that will extract these programs automatically in this folder, before running the demonstration.
