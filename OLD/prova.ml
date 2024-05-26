needs "Ntrie/ntrie.ml";;

`%%(1 7 2 10)`;;
dest_comb it;;

type_of `%%(1 7 2 10)`;;
NTRIE_REDUCE_CONV `42 INSERT %%(1 7 2 10) UNION %%(12 6 2)`;;

search[name "JORDAN"];;