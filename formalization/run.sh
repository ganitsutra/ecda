#!/bin/bash
currentver="$(coqc --version | head -n1 | cut -d" " -f6)"
echo "\nCoq version ${currentver} found on this system\n"

printf "\n**********First compiling libraries from the earlier works********** ...\n\n"
printf "\nCompiling basic list libraries...\n\n"

if [ "$(printf '%s\n' "8.16.0" "$currentver" | sort -V | head -n1)" = "8.16.0" ]; then 

coqc -w "-all" -compat 8.14 NSS2021_lib.v

printf "Compiling definitions and lemmas...\n\n"

coqc -w "-all" -compat 8.14 Definitions.v

coqc -w "-all" -compat 8.14 Properties.v

printf "Compiling maximum matching theorem...\n\n"
coqc -w "-all" -compat 8.14 MaxMatch.v

printf "Compiling local and global uniqueness theorems...\n\n"
coqc -w "-all" -compat 8.14 UniqueMatch.v

printf "Compiling algorithm and its correctness...\n\n"
coqc -w "-all" -compat 8.14 Programs.v

printf "Completed compiling all the files associated with the earlier works.\n\n"
printf "\n**********Now compiling our efficient formalization ********** ...\n\n"
coqc -w "-all" -compat 8.14 RBT.v
coqc -w "-all" -compat 8.14 OTypes.v
coqc -w "-all" -compat 8.14 Efficient.v

elif [ "$(printf '%s\n' "8.15.0" "$currentver" | sort -V | head -n1)" = "8.15.0" ]; then 

coqc -w "-all" -compat 8.13 NSS2021_lib.v

printf "Compiling definitions and lemmas...\n\n"

coqc -w "-all" -compat 8.13 Definitions.v

coqc -w "-all" -compat 8.13 Properties.v

printf "Compiling maximum matching theorem...\n\n"
coqc -w "-all" -compat 8.13 MaxMatch.v

printf "Compiling local and global uniqueness theorems...\n\n"
coqc -w "-all" -compat 8.13 UniqueMatch.v

printf "Compiling algorithm and its correctness...\n\n"
coqc -w "-all" -compat 8.13 Programs.v

printf "Completed compiling all the files associated with the earlier works.\n\n"
printf "\n**********Now compiling our efficient formalization ********** ...\n\n"
coqc -w "-all" -compat 8.13 RBT.v
coqc -w "-all" -compat 8.13 OTypes.v
coqc -w "-all" -compat 8.13 Efficient.v

elif [ "$(printf '%s\n' "8.14.0" "$currentver" | sort -V | head -n1)" = "8.14.0" ]; then 

coqc -w "-all" -compat 8.12 NSS2021_lib.v

printf "Compiling definitions and lemmas...\n\n"

coqc -w "-all" -compat 8.12 Definitions.v

coqc -w "-all" -compat 8.12 Properties.v

printf "Compiling maximum matching theorem...\n\n"
coqc -w "-all" -compat 8.12 MaxMatch.v

printf "Compiling local and global uniqueness theorems...\n\n"
coqc -w "-all" -compat 8.12 UniqueMatch.v

printf "Compiling algorithm and its correctness...\n\n"
coqc -w "-all" -compat 8.12 Programs.v

printf "Completed compiling all the files associated with the earlier works.\n\n"
printf "\n**********Now compiling our efficient formalization ********** ...\n\n"
coqc -w "-all" -compat 8.12 RBT.v
coqc -w "-all" -compat 8.12 OTypes.v
coqc -w "-all" -compat 8.12 Efficient.v

elif [ "$(printf '%s\n' "8.13.0" "$currentver" | sort -V | head -n1)" = "8.13.0" ]; then 

coqc -w "-all" -compat 8.12 NSS2021_lib.v

printf "Compiling definitions and lemmas...\n\n"

coqc -w "-all" -compat 8.12 Definitions.v

coqc -w "-all" -compat 8.12 Properties.v

printf "Compiling maximum matching theorem...\n\n"
coqc -w "-all" -compat 8.12 MaxMatch.v

printf "Compiling local and global uniqueness theorems...\n\n"
coqc -w "-all" -compat 8.12 UniqueMatch.v

printf "Compiling algorithm and its correctness...\n\n"
coqc -w "-all" -compat 8.12 Programs.v

printf "Completed compiling all the files associated with the earlier works.\n\n"
printf "\n**********Now compiling our efficient formalization ********** ...\n\n"
coqc -w "-all" -compat 8.12 RBT.v
coqc -w "-all" -compat 8.12 OTypes.v
coqc -w "-all" -compat 8.12 Efficient.v

else

coqc -w "-all" NSS2021_lib.v

printf "Compiling definitions and lemmas...\n\n"

coqc -w "-all" Definitions.v

coqc -w "-all" Properties.v

printf "Compiling maximum matching theorem...\n\n"
coqc -w "-all"MaxMatch.v

printf "Compiling local and global uniqueness theorems...\n\n"
coqc -w "-all"UniqueMatch.v

printf "Compiling algorithm and its correctness...\n\n"
coqc -w "-all"Programs.v

printf "Completed compiling all the files associated with the earlier works.\n\n"
printf "\n**********Now compiling our efficient formalization ********** ...\n\n"
coqc -w "-all" RBT.v
coqc -w "-all" OTypes.v
coqc -w "-all" Efficient.v

fi

printf "Completed compiling all the files!\n\n"

printf "Extracted OCaml programs are in the '../application' folder!\n\n"



