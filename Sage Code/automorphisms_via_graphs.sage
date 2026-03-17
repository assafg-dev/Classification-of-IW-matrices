from typing import Set


def block_from_entry(a):
    if a>=0:
        return a*identity_matrix(2)
    else:
        return -a*matrix(2,[0,1,1,0])
        
def extended_matrix(M):
    n=M.nrows()
    LEM=map(block_from_entry, M.list())
    return block_matrix(n,list(LEM))

def extended_automorphism_group(M):
    EM=extended_matrix(M.transpose())
    GrEM=BipartiteGraph(EM,multiedges=True)
    pi=SymmetricGroup(domain=range(4*M.nrows()))(sum([[2*i,2*i+1] for i in range(M.nrows())],[])+list(range(2*M.nrows(),4*M.nrows())))
    ExG=GrEM.automorphism_group(edge_labels=True)
    return ExG.centralizer(pi)

def unsigned_automorphism_group(M):
    EM=M.transpose()
    GrEM=BipartiteGraph(EM,multiedges=True)
    ExG=GrEM.automorphism_group(edge_labels=True)
    return ExG

def an_automorphism(M,ExtAut=None):
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

def an_automorphism_old(M,ExtAut=None):
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
    
def automorphism_group_hadamard(M):
    n=M.nrows()
    EM=extended_matrix(M)
    Z=0*EM
    M2=block_matrix(2,[Z,EM,Z,Z])
    G=DiGraph(M2,multiedges=True)
    Sn=SymmetricGroup(domain=range(0,4*n))
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
    return Aut

def an_isomorphism(M,N,ExtAut=None):
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

import subprocess
import re

def automorphism_group_graph_nauty(G):
    """
    Compute the automorphism group of a graph using the nauty package. 
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
    dread_input += "x,b,q \n"

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
    return PermutationGroup(perms)

def convert_weighted_graph_to_unweighted_lazy_form(DG):
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

def convert_weighted_graph_to_unweighted(DG):
    """
    This is the binary extension of the graph DG to a multi-layer graph, to account for edge labelling. If the edges are labelled by a set of colors corresponding to a subset of {0,1,2,...,2^r-1}, then we add b layers. Each layer contains a copy of the set of vertices, and each vertex is connected to the corresponding vertex in the next layer. Then, for each edge (a,b) of color c we connect the corresponding copies of a and b, in the layers that correspond to the 1's in the binary expansion of c. This way, we can use nauty to compute automorphisms of weighted graphs, and we get exactly the automorphisms that preserve the edge labels. 
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
        
        
    
    