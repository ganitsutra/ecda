open Str

(**Read data from a file**)
let read_line ic = try Some (input_line ic) with End_of_file -> None
let lines_from_files filename =
  let rec lines_from_files_aux ic acc = match (read_line ic) with
    | None -> List.rev acc             (*To output in the same order, please do List.rev acc *)
    | Some s -> lines_from_files_aux ic (s :: acc) in
  lines_from_files_aux (open_in filename) []
  
(**#########Functions to read instructions data from the file##########**)

(** 1. This function converts a string into command**)
let convert_to_command s = match s with
|"Buy" -> Extracted_list.Buy
|"Sell" -> Extracted_list.Sell
|"Del" -> Extracted_list.Del
|_ -> raise (Invalid_argument "Command information is incomplete/incorrect")

(** 2. This function converts a list of 5 length string into an instruction**)
let create_instruction l=
        match l with
                |[c;i;t;q;p] -> {Extracted_list.cmd = convert_to_command c; Extracted_list.ord ={ Extracted_list.id =  int_of_string i; Extracted_list.otime = int_of_string t; 
                Extracted_list.oprice = int_of_string p;Extracted_list.oquantity = int_of_string q }}
                |_ ->raise (Invalid_argument "instruction information is incomplete");;

(** 3. This function split a string by comma ',' **)
let string_to_tuple line=create_instruction (String.split_on_char ',' line);;


(**4. This function takes a list of strings and converts them into list of instructions*)
(*let rec str_list_to_instructions mylist= match mylist with
        | [] ->[]
        | line::mylist' ->(string_to_tuple line)::(str_list_to_instructions mylist') *)

(** using map **) (**f := (string_to_tuple) and l := mylist  map:= str_list_to_instructions **)
let map f l = 
  let rec map_aux acc = function
    | [] -> acc []
    | x :: xs -> map_aux (fun ys -> acc (f x :: ys)) xs
  in
  map_aux (fun ys -> ys) l

(**5. Read input data and converts them into list of instructions**)


(**6. function to print a matching**)



let rec printmfile oc (m:Extracted_list.transaction list) = match m with 
  |[] -> ()
  |[f] -> Printf.fprintf oc "%d,%d,%d\n" f.idb f.ida f.tquantity
  |f::m' -> Printf.fprintf oc "%d,%d,%d;" f.idb f.ida f.tquantity; printmfile oc m' 

let writematching file (m:Extracted_list.transaction list) =
  let oc = open_out file in
  printmfile oc m ;
  close_out oc;;



let ploop p lst oc =
	let combiner acc x =
		let output = p (Extracted_list.blist acc) (Extracted_list.alist acc) x in 
		(printmfile oc (Extracted_list.mlist output)); output
	in
	let init = (([],[]),[])
	in
	List.fold_left combiner init lst ;;
(**
let rec ploop p i k oc=
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> let output = (([],[]),[]) in (printmfile oc (Extracted_list.mlist output) 0); output )
    (fun k' ->
    let output = (let it = ploop p i k' oc in
    p (Extracted_list.blist it) (Extracted_list.alist it) (Extracted_list.nth k' i Extracted_list.tau0))  in (printmfile oc (Extracted_list.mlist output) (k'+1)); output   ) 
    k 
**)


(**Comparison part**)


(**########These functions compare two matchings m1 m2##############**)
let lexicographic_compare (x:Extracted_list.transaction) (y:Extracted_list.transaction) =
  let compare_fst = compare x.idb y.idb in
  if compare_fst <> 0 then compare_fst
  else compare x.ida y.ida

let compare_matchings m1 m2 = (List.sort lexicographic_compare m1) = (List.sort lexicographic_compare m2) 

(** 1. This function converts a list of 3 length string into a transaction**)
let create_transaction l =
        match l with
                |[i;j;q] -> {Extracted_list.idb = int_of_string i; Extracted_list.ida = int_of_string j; Extracted_list.tquantity = int_of_string q }
                |_ ->raise (Invalid_argument "instruction information is incomplete");;

(** 2. This function split a string by comma ',' **)
let string_to_transaction line = create_transaction (String.split_on_char ',' line);;


(**3. This function takes a list of strings and converts them into list of transactions*)
let rec str_list_to_trnsactions mylist = match mylist with
        | [] ->[]
        | line::mylist' ->(string_to_transaction line)::(str_list_to_trnsactions mylist')

(** 4. This function split a string by colon ';' **)
let string_to_transaction_list line = str_list_to_trnsactions (String.split_on_char ';' line);;

(**3. This function takes a list of strings and converts them into list of transactions*)
let rec printm (m:Extracted_list.transaction list) str = match m with
	|[] -> ()
	|[a] -> (Printf.printf "This is %s output: Buy id: %i, Sell id: %i, Quantity: %i \n" str a.idb a.ida a.tquantity)
	|a::m' -> (Printf.printf "Buy id: %i, Sell id: %i, Quantity: %i\n" a.idb a.ida a.tquantity);printm m' str;;

(**Now apply string_to_transaction_list recursivelly on each line of the two files parallely. Then use b= compare_matchings with cform(m1) and cform(m2)
If b is two output matched at ... else terminate and output not matched for the ids i and j**)


let rec compare_outputs l1 l2 k = match (l1, l2) with
|(line1::l1', line2::l2') -> let m1 = string_to_transaction_list line1 in
			   let m2 = string_to_transaction_list line2 in
			   let b = compare_matchings (Extracted_list.cform m1) (Extracted_list.cform m2) in
			    if b then compare_outputs l1' l2' (k+1) else 
			    (Printf.printf "Not matched: output number %d\n" k;printm m1 "verified";printm m2 "exchange")
|([], line2::l2') -> Printf.printf "Not matched: Trade volume produced by the exchange is greater than the trade volume produced by the verified algorithm.\n"
|(line1::l1', []) -> Printf.printf "Not matched: Trade volume produced by the verified algorithm is greater than the trade volume produced by the exchange.\n"
|([], [])-> Printf.printf "No mismatch found.\n"



(**Input/Ouput**)


let iorderfile = Sys.argv.(1) ;;

let orderbook = map (string_to_tuple) (lines_from_files iorderfile );;
(**f := (string_to_tuple) and l := 
mylist  map:= str_list_to_instructions **)

let m = List.length orderbook;;
Printf.printf "\n%s contains %d instructions.\n" iorderfile m;;
let ofile = "verified_" ^ Sys.argv.(1) ;;


let () = let oc = open_out ofile in
ignore (ploop (Extracted_list.process_instruction) orderbook oc) ; close_out oc;;

Printf.printf "\nVerified transactions succesfully created and saved in %s.\n\n" ofile ;;

Printf.printf "\nComparison finished.\n\n" ;;
