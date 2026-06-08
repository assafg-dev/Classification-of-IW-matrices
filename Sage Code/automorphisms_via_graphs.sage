from typing import Set


def block_from_entry(a): ## Set up the 2x2 block for the Hadamard graph.
    if a>=0:
        return a*identity_matrix(2)
    else:
        return -a*matrix(2,[0,1,1,0])
        
def extended_matrix(M): ## This is the (weighted) Hadamard graph obtained from the integer matrix M.
    n=M.nrows()
    LEM=map(block_from_entry, M.list())
    return block_matrix(n,list(LEM))

def extended_automorphism_group(M):
    """
    Compute the automorphism group of the wieghted Hadamard graph associated to M, and return the subgroup that reduces to the (H-equivallence) automorphism group of M. 
    
    Input: An integer matrix M.
    Output: The group of automorphisms of M as a permutation group inside the automorphism group of the extended matrix (Hadamard graph) EM.
    """
    EM=extended_matrix(M.transpose())
    GrEM=BipartiteGraph(EM,multiedges=True)
    pi=SymmetricGroup(domain=range(4*M.nrows()))(sum([[2*i,2*i+1] for i in range(M.nrows())],[])+list(range(2*M.nrows(),4*M.nrows())))
    ExG=GrEM.automorphism_group(edge_labels=True)
    return ExG.centralizer(pi)

def unsigned_automorphism_group(M): ### Compute the unsigned (=permutation) automorphism group of M. 
    MT=M.transpose()
    GrEM=BipartiteGraph(MT,multiedges=True)
    ExG=GrEM.automorphism_group(edge_labels=True)
    return ExG

def an_automorphism(M):
    """
    Find a random automorphism of M.

    Input: An integer matrix M.

    Output: A pair of matrices (L,R) such that L*M*R.transpose()==M
    """
    n=M.nrows()
    Sn=SymmetricGroup(domain=range(n))
    pi=Sn.random_element()
    sig=Sn.random_element()
    L1=pi.matrix()*diagonal_matrix([2*randrange(2)-1 for r in range(n)])
    R1=sig.matrix()
    M1=L1*M*R1.transpose()
    L2,R2=an_isomorphism(M,M1,ExtAut)
    L=L2.transpose()*L1
    R=R2.transpose()*R1
    assert L*M*R.transpose()==M
    return L,R


    #return an_isomorphism(M,M,ExtAut)

def an_automorphism_old(M,ExtAut=None): ### This is an old function and is not used anymore.
    n=M.nrows()
    if not(ExtAut):
        ExtAut=extended_automorphism_group(M)
    good=False
    while(not(good)):
        sigma=ExtAut.random_element()
        if sigma(0)<2*n:
            good=True
    L=matrix(ZZ,n)
    R=matrix(ZZ,n)
    for i in range(n):
        j=sigma(2*i)
        k=sigma(2*i+1)
        if max(j,k)>=2*n:
            return False
        if ZZ(j-k).abs()==1:
            if j<k:
                L[i,j/2]=1
            else:
                L[i,k/2]=-1
        j=sigma(2*i+2*n)-2*n
        k=sigma(2*i+1+2*n)-2*n
        if ZZ(j-k).abs()==1:
            if j<k:
                R[i,j/2]=1
            else:
                R[i,k/2]=-1 
    if L*M*R.transpose()==M:
        return L,R
    else:
        return False
    
def automorphism_group_hadamard(M,id=False):  ### Compute the automorphism group of an IW matrix M using the 'nauty' program.
    """
    Compute the automorphism group of an IW matrix M using the 'nauty' program.

    Input: An IW matrix M. If id=True, also return the identifier of Hadamard graph as given by 'nauty'. This id is the same for isomorphic matrices, although rarely two non-isomorphic matrices can have the same id.

    Output: The automorphism group of M as a monomial matrix group given by the projection to the left matrix. If id=True return the identifier of M as a string.    
    """
    n=M.nrows()
    EM=extended_matrix(M)
    Z=0*EM
    M2=block_matrix(2,[Z,EM,Z,Z])
    G=DiGraph(M2,multiedges=True)
    Sn=SymmetricGroup(domain=range(0,4*n))
    if id:
        AutGraph,Id=automorphism_group_graph_nauty(G,id=True)
    else:
        AutGraph=automorphism_group_graph_nauty(G)
    pi=Sn(sum([[2*i,2*i+1] for i in range(n)],[])+list(range(2*n,4*n)))
    AutP=AutGraph.centralizer(pi)
    S=set(range(2*n))
    AutP=AutP.stabilizer(S,action='OnSets')
    #print(f'Automorphism group cardinality: {AutP.cardinality()}')
    Aut_gens=[]
    for perm in AutP.gens():
        #print(f'{sigma=}')
        isom=perm
        #print(isom)
        L=matrix(ZZ,n)
        R=matrix(ZZ,n)
        for i in range(n):
            j=isom(2*i)
            k=isom(2*i+1)
            if ZZ(j-k).abs()==1:
                if j<k:
                    L[i,(j)/2]=1
                else:
                    L[i,(k)/2]=-1
            j=isom(2*i+2*n)-2*n
            k=isom(2*i+2*n+1)-2*n
            if ZZ(j-k).abs()==1:
                if j<k:
                    R[i,(j)/2]=1
                else:
                    R[i,(k)/2]=-1  
        assert L*M*R.transpose()==M
        Aut_gens.append(L)
    Aut=MatrixGroup(Aut_gens)
    if id:
        return Aut,Id
    else:
        return Aut

def an_isomorphism(M,N,ExtAut=None):
    """
    Find a random isomorphism between M and N.

    Input: Integer matrices M and N.
           If ExtAut is given, it should be the automorphism group of M, as computed by extended_automorphism_group(M). If not given, it will be computed inside the function.

    Output: A pair of matrices (L,R) such that L*M*R.transpose()==N. If no such isomorphism exists, return False.
    """
    
    n=M.nrows()
    Sn=SymmetricGroup(domain=range(4*n))
    if not(ExtAut):
        ExtAut=extended_automorphism_group(M)
    EM=extended_matrix(M.transpose())
    EN=extended_matrix(N.transpose())
    GrEM=BipartiteGraph(EM,multiedges=True)
    GrEN=BipartiteGraph(EN,multiedges=True)
    T,cert=GrEM.is_isomorphic(GrEN,certificate=True)
    #print(f'{cert=}')
    if not(T):
        #print('reason 1')
        return False
    lisom=[xx[1] for xx in sorted(cert.items())]
    isom0=Sn(lisom)^-1
    
    
    found=False
    #print(f'{Sn(list(cert.values()))^-1=}')
    for sigma in ExtAut:
        #print(f'{sigma=}')
        false_isom=False
        isom=isom0*sigma
       # print(f'isom(0)={isom(0)}')
        if isom(0)<2*n:
            found=True
           # break
        if not(found):
            continue
        #print(isom)
        L=matrix(ZZ,n)
        R=matrix(ZZ,n)
        for i in range(n):
            j=isom(2*i)
            k=isom(2*i+1)
            if max(j,k)>=2*n:
                #print('here')
                false_isom=True
                break
            if ZZ(j-k).abs()==1:
                if j<k:
                    #print(i,j,k)
                    L[i,j/2]=1
                else:
                    #print(k)
                    L[i,k/2]=-1
            j=isom(2*i+2*n)-2*n
            k=isom(2*i+1+2*n)-2*n
            if ZZ(j-k).abs()==1:
                if j<k:
                    R[i,j/2]=1
                else:
                    R[i,k/2]=-1  
        #print(false_isom)
        if false_isom:
            continue
        if L*M*R.transpose()==N:
            return L,R
    return False

def find_isomorphism_hadamard(M1,M2,certificate=False):
    """
    Check if M1 and M2 are isomorphic. If they are, optionally return the isomorphism. This function uses the 'nauty' program. 

    Input: Two IW matrices M1 and M2 and a boolean certificate=False. 

    Output: A boolean True if M1 and M2 are isomorphic, and False otherwise. If certificate=True, return the isomorphism as a pair of matrices (L,R) such that L*M1*R.transpose()==M2. 
    
    """
    n=M1.nrows()
    EM1=extended_matrix(M1)
    EM2=extended_matrix(M2)
    Z=0*EM1
    MM1=block_matrix(2,[Z,EM1,Z,Z])
    MM2=block_matrix(2,[Z,EM2,Z,Z])
    G1=DiGraph(MM1,multiedges=True)
    G2=DiGraph(MM2,multiedges=True)
    isom=isomorphism_graph_nauty(G1,G2,certificate=certificate,part1=f'[{0}:{2*n-1}]',part2=f'[{0}:{2*n-1}]')
    if not(isom):
        return False
    if not(certificate):
        return True
    L=matrix(ZZ,n)
    R=matrix(ZZ,n)
    for i in range(n):
        j=isom(2*i)
        k=isom(2*i+1)
        if ZZ(j-k).abs()==1:
            if j<k:
                L[i,(j)/2]=1
            else:
                L[i,(k)/2]=-1
        j=isom(2*i+2*n)-2*n
        k=isom(2*i+2*n+1)-2*n
        if ZZ(j-k).abs()==1:
            if j<k:
                R[i,(j)/2]=1
            else:
                R[i,(k)/2]=-1  
    assert L*M2*R.transpose()==M1
    return L.transpose(),R  ## TODO: Originally it was written here R.transpose(), but R should be the correct choice.




import subprocess
import re

def automorphism_group_graph_nauty(G,id=False):
    """
    Compute the automorphism group of a graph using the 'nauty' package. This is used in other functions to find the H-equivalence automorphism group of IW matrices.

    Input: A graph G and a boolean id=False. 

    Output: The automorphism group of G as a permutation group. If id=True, also return the identifier of G as a string. The identifier is the same for isomorphic graphs, although rarely two non-isomorphic graphs can have the same identifier.
    """
   

    # 1. Prepare the dreadnaut input string
    n = G.order()
    M=G.adjacency_matrix()
    labels=set(M.list())
    if len(labels)>=2: # Use this to treat the weighted graph case.
        G,partition=convert_weighted_graph_to_unweighted(G)
        weighted=True
    else: weighted=False
    m = G.order()
    # 'n=X' sets number of vertices
    # 'g' starts the graph input
    dread_input = f"n={m} g\n"
    
    # Add the adjacency list (dreadnaut uses : to terminate each vertex list)
    for v in range(m):
        neighbors = " ".join(map(str, G.neighbors(v)))
        dread_input += f" {v} : {neighbors} ;\n"
    if weighted: # In the weighted case, prepare the partition into the first block of the original n vertices, and each one of the rest of the new vertices. Nauty will only compute automorphisms that preserve this partition.
        #partition=f'[{0}:{n-1}'
        #for v in new_vertices:
        #    partition+=f'|{v}]'
        #partition+=']'
        dread_input+=f'f={partition}\n'
            
    # 'x' executes the automorphism calculation
    # 'b' prints the generators
    # 'q' quits
    dread_input += "c,x,z,b,q \n"

    # 2. Call the subprocess
    # Note: Ensure 'dreadnaut' is in your system PATH
    process = subprocess.Popen(
        ['dreadnaut'], 
        stdin=subprocess.PIPE, 
        stdout=subprocess.PIPE, 
        stderr=subprocess.PIPE, 
        text=True
    )
    
    stdout, stderr = process.communicate(input=dread_input)
    #if stderr:
    #    print("Error:", stderr)
    
    ### This code extracts the generators from the nauty output.
    match = re.findall(r"\([\d+\s]*\)|\n\s*",stdout)
    perms=[]
    perm=[]
    for m in match:
        if m[0]=='(':
            p=tuple(map(int, re.split(r'\s+|\n',m[1:-1])))
            perm.append(p)
        if m=='\n':
            perms.append(perm)
            perm=[]
    if not(id):
        return PermutationGroup(perms)
    else:
        match = re.search(r"\n\[[0-9a-zA-Z\s]*\]",stdout)
        Id=match.group()[1:]
        return PermutationGroup(perms),Id

def isomorphism_graph_nauty(G1, G2,part1=None,part2=None,certificate=False):
    """
    Compute an isomorphism between two sage weighted
    graphs using the 'nauty' program.

    Input: Sage weighted graphs G1 and G2 
        
           part1 and part2 are two matching partitions on G1 and G2 which the isomorphism should preserve. They should be given in the format of a string like '[0:3|4:7|8:11]', which means that the vertices 0,1,2,3 are in one block, 4,5,6,7 are in another block, and 8,9,10,11 are in another block. If part1 and part2 are not given, then no partition is used.

           certificate = False, a boolean.

    Output: A boolean True if G1 and G2 are isomorphic, and False otherwise. If certificate=True, return the isomorphism as a permutation.
    
    A permutation that gives the isomorphism. 
    """
   
    
    relabels=[]
    M1=G1.adjacency_matrix()
    M2=G2.adjacency_matrix()
    labels1=set(M1.list())
    labels2=set(M2.list())
    if len(labels1)!=len(labels2): 
        return False
    if len(labels1)>=2: # Use this to treat the weighted graph case.
        G1,partition1=convert_weighted_graph_to_unweighted(G1)
        G2,partition2=convert_weighted_graph_to_unweighted(G2)
        weighted=True
    else: weighted=False
    if part1 and part2:
        partition1=part1
        partition2=part2
    ord=G1.order()
    Sn=SymmetricGroup(domain=range(ord))
    canonL=[]
    for G,partition in [(G1,partition1),(G2,partition2)]:
        m = G.order()
        # 'n=X' sets number of vertices
        # 'g' starts the graph input
        dread_input = f"n={m} g\n"
        
        # Add the adjacency list (dreadnaut uses : to terminate each vertex list)
        for v in range(m):
            neighbors = " ".join(map(str, G.neighbors(v)))
            dread_input += f" {v} : {neighbors} ;\n"
        if weighted: # In the weighted case, prepare the partition into the first block of the original n vertices, and each one of the rest of the new vertices. Nauty will only compute automorphisms that preserve this partition.
            #partition=f'[{0}:{n-1}'
            #for v in new_vertices:
            #    partition+=f'|{v}]'
            #partition+=']'
            dread_input+=f'f={partition}\n'
                
        # 'x' executes the automorphism calculation
        # 'b' prints the generators
        # 'q' quits
        dread_input += "c,x,b,q \n"

        # 2. Call the subprocess
        # Note: Ensure 'dreadnaut' is in your system PATH
        process = subprocess.Popen(
            ['dreadnaut'], 
            stdin=subprocess.PIPE, 
            stdout=subprocess.PIPE, 
            stderr=subprocess.PIPE, 
            text=True
        )
        
        stdout, stderr = process.communicate(input=dread_input)
    #if stderr:
    #    print("Error:", stderr)
    
    ### This code extracts the generators from the nauty output.
        match = re.search(r"seconds\n[\d+\s]+\n",stdout)
        raw=match.group()[8:]
        raw=re.sub(r"\s+",",",raw)
        rawl=raw.split(',')[1:-1]
        if certificate:
            relabels.append(Sn(list(map(ZZ, rawl))))
        #print(f'{relabel=}')
        canonG=re.findall(r"\d+ :  [\d+\s]*;\n",stdout)
        canonL.append(canonG)
    if canonL[0]!=canonL[1]:    
        return False
    else:
        if certificate:
            perm=relabels[0]^-1*relabels[1]
            return perm  ##TODO compute the true permutation.
        else:
            return True 
       


def convert_weighted_graph_to_unweighted_lazy_form(DG):  ### This is an old an unsuccessful function to persuade 'nauty' to compute automorphisms and isomorphisms of weighted graphs. Not used  anymore.
    """
    This adds a vertex to each edge label, and connects it to all vertices that have that label in their row or column in the adjacency matrix. This way we can use nauty to compute automorphisms of weighted graphs. It refines the graph according to the label partition, but there could still be some extra automorphisms. 
    """
    G=DG.copy(immutable=False)
    M=G.adjacency_matrix()
    V=G.vertices()
    n=G.order()
    labels=set(M.list())
    for i,l in enumerate(labels):
        G.add_vertex(name=i+n)
        G.add_edges([(v,i+n) for v in V if list(M.row(v)).count(l)>0 or list(M.column(v)).count(l)>0])
    new_vertices=set(G.vertices())-set(V)
    return G,new_vertices

def convert_weighted_graph_to_unweighted(DG): ### This function is used to persuade 'nauty' to compute automorphisms and isomorphisms of weighted graphs, by converting them to a rich enough unweighted graphs from which the isomorphisms can be read off. 
    """
    This is the binary extension of the graph DG to a multi-layer graph, to account for edge labelling. If the edges are labelled by a set of colors corresponding to a subset of {0,1,2,...,2^r-1}, then we add b layers. Each layer contains a copy of the set of vertices, and each vertex is connected to the corresponding vertex in the next layer. Then, for each edge (a,b) of color c we connect the corresponding copies of a and b, in the layers that correspond to the 1's in the binary expansion of c. This way, we can use 'nauty' to compute automorphisms of weighted graphs, and we get exactly the automorphisms that preserve the edge labels. 
    """ 

    G=DG.copy(immutable=False)
    M=G.adjacency_matrix()
    V=G.vertices()
    n=G.order()
    labels=list(set(M.list()))
    r=ZZ(labels[-1]).nbits() # Number of bits needed to represent the largest label
    for i in range(1,r):
        G.add_vertices([v+n*i for v in V])
        G.add_edges([(v+n*(i-1),v+n*i) for v in V])
    for a in V:
        for b in V:
            c=M[a,b]
            if c==0:
                continue
            d=ZZ(c).bits()
            d=d+[0]*(r-len(d)) # Binary expansion of the label, padded with zeros
            for i in range(r):
                if d[i]==1:
                    G.add_edge(a+n*i,b+n*i)
    partition=f'[{0}:{n-1}]'
    return G,partition
        
        
    
    