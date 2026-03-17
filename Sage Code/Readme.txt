This is the sage code for computing various classification tasks of integer weighing matrices. 
In Sage you should load the file 'automorphism_groups.sage' and this will load the rest of the files.

Main tasks to perform:

1) Classify all primitive integer IW matrices:  classify_primitive_IW(n,w,b=,max_entry=)
2) Compute the automorphism group of a primitive matrix: automorphism_group(M,proof=True,base=,algorithm=) 
3) Generate a json file with the classification data. Performs the above two tasks and compute class representatives, automorphism groups, generators of the groups, and cardinalities.
4) Count the number of symmetric and antisymmetric members in a class: count_sym_and_antisym_matrices(A,b=,Aut=,ngens=,base=) 
5) Classify the symmetric and antisymmetric SH-equivalence classes in a given H-class: classification_list_symm_and_antisymm(M,Aut=)
