load('BackTracking3.sage')
load('PermsBetweenMatrices.sage')
load('Classification.sage')
load('automorphisms_via_graphs.sage')

from itertools import product
from collections import Counter


def read_permutation_group(s):
    l=s.split('),')
    l=[x+')' for x in l[:-1]]+[l[-1]]
    return PermutationGroup(l)

### This function computes a subgroup of the automorphism group of an IW A. This is done by randomly generating automorphisms. The result is probably the full automorphism group, but this is not guaranteed.
def approximate_automorphism_group(A,ngens=6):
    """ 
    Compute a subgroup of automorphisms of A by randomly adjoining ngens elements.
        In most cases this is the The result is probably the full automorphism group, but this is not guaranteed. The function returns the left side of this automorphism subgroup. To find the right counterpart of each left item L, use L=find_R_from_L(A,L).
    """
    #b=min(b,A.ncols())
    n=A.nrows()
    In=identity_matrix(ZZ,n)
    Aut=[-In] # This is always an automorphism.
    GeM=extended_automorphism_group(A) # This is the permutation automorphism group of the extended matrix.
    for _ in range(ngens):
        LR=an_automorphism(A,ExtAut=GeM) # Compute a random automorphism of A (left and right side).
        if not(LR):
            continue
        #print('automorphism found')
        LL=LR[0] # Left side of the automorphism.
        #print(f'L={LL}')
        Aut.append(LL)
    GG=GL(A.nrows(),ZZ)
    HH=GG.subgroup(GG(X) for X in Aut) # Form the matrix subgroup of all left side automorphisms. 
    return HH

def min_gen_set(G):
    """
    Find a minimal generating set of a matrix subgroup G of GL(n,ZZ). The function returns the list of generators in this minimal generating set. Wraps the similar function minimal_generating_set for permutation groups.
    """
    H=G.as_permutation_group()
    gensH=H.minimal_generating_set()
    phi=H.hom(G)
    return list(map(phi,gensH))

def mon_to_sign_perm(N):
    """
    Convert a sign monomial matrix N the line code of the corresponding signed permutation, which is the tuple of the form (s1*i1,s2*i2,...,sn*in), where si is the sign of the i-th column of N and ij is the index of the image of j.
    """
    M=N
    if not(hasattr(N,'nrows')):
        M=N.matrix()
    n=M.nrows()
    s=sum(M.transpose())
    P=diagonal_matrix(s)*M
    char=[]
    for i in range(n):
        j=s[i]*(list(P.row(i)).index(1)+1)
        char.append(j)
    return tuple(char)

def find_R_from_L(A,L,base=10):
    """
    Given a left side L of an automorphism of A, this function finds the right side R such that (L,R) is an automorphism of A. The function returns R.
    """
    L1=L
    if hasattr(L,'matrix'):
        L1=L.matrix()
    R=find_L_from_R(A.transpose(),L1.transpose(),base).transpose()
    return R

def generating_set_of_automorphisms(A,G):
    """
    Return a list of signed permutations given in (left,right) pairs of line codes, generating the given  automorphism subgroup G of A (given by its left side). 
    """
    min_gens=min_gen_set(G)
    Rights=[find_R_from_L(A,LL) for LL in min_gens]
    return [(mon_to_sign_perm(LL),mon_to_sign_perm(RR)) for LL,RR in zip(min_gens,Rights)]
        

#### Here we classify the IW matrices up to equivalence. ####

def is_primitive(A):
    """
    Returns True if and only if A is a primitive matrix. Otherwise, it returns False.
    """
    n=A.nrows()
    Gr=DiGraph(A)
    return Gr.is_connected()

def test_equivalence_old(A,B,b=4,d=1):  ### This is an old version of the Hadamard equivalence test. Not used here.
    try:
        equiv=Are_Equivalent(A,B,b,d)
    except ValueError:
        equiv=Are_Equivalent(A,B,b,d+1)
    if equiv:
        return equiv
    return False

def test_equivalence(A,B,b=3,algorithm=None,certificate=False):
    """
    Test if A and B are Hadamard equivalent. The parameter b=3 is the code invariant depth computed for A and B to try to tell them apart. Only if the codes are the same, we proceed to the full test of isomorphism.look for an isomorphism. If certificate=True, return the isomorphism as a pair (L,R) of monomial matrices such that L*A*R.transpose()==B. The defualt algorithm=None uses the sage implementation of the graph isomorphism. We can set algorithm=='nauty', in which case the code invariant is not computed and the program uses the nauty software to decide this question. This option relies on nauty, without further proof, and is faster when applied to large matrices, e.g. of size 100.
    """
    if algorithm=='nauty':
        isom=find_isomorphism_hadamard(A,B,certificate=certificate)
        return isom
    isom=an_isomorphism(A,B)
    if isom:
        return isom
    elif nCount(A,b)!=nCount(B,b):
        return False

def classify_by_code(Matrices,b=4):
    """
    Given a list of matrices, we classify them by equating their code invariants of depth b. This is an initial step of classification. The function returns a dictionary of code to list of matrices. Subsequently we classify up to H-equivalence each list separately by the function classify_primitive_IW.

    Input: Matrices = a list of IW matrices, 
    b=4: The depth of the code invariant.
     
    Output: A dictionary of code to list.
    """
    code_classes={}
    for A in Matrices:
        if is_primitive(A):
            codeA=nCount(A,b)
            code_classes.setdefault(tuple(codeA),[]).append(A)
    return code_classes

def classify_primitive_IW(n,w,b=3,exhaustive_list=False, max_entry=Infinity):
    """
    classify all primitive IW matrices of order n and weight w, up to H-equivalence.
     Input: n = order,
        w = weight,
        b = depth of code invariant, set to 3 for efficiency.
        exhaustive_list = List of matrices to classify. Could be some partial list, e.g. those of the same code invariant. If False, we use the classification procedure ExhaustiveListIW, and classify all the IW matrices of the given parameters.
        max_entry = maximum entry in absolute value that is allowed to appear in the matrix. By default there is no limit. For classical weighing matrices set max_entry=1.

    Output: A list of representatives of the equivalence classes, one per each class.
    """
    code_classes=classify_by_code(ExhaustiveListIW(n,w,max_entry=max_entry) if not(exhaustive_list) else exhaustive_list,b)
    #print(f'Number of code classes: {len(code_classes)}')
    equiv_classes=[]
    count=0
    for mat_list in code_classes.values():
        count+=1
        #print(f'code number={count}')
        code_equiv_classes=[mat_list[0]]
        for M in mat_list[1:]:
            found_M=False
            for N in code_equiv_classes:
                if test_equivalence(M,N,b=b):
                    found_M=True
                    break
            if not(found_M):
                code_equiv_classes.append(M)
        equiv_classes.extend(copy(code_equiv_classes))
        #print(f'so far collectd {len(equiv_classes)} inequivalent matrices')
    return equiv_classes

def transpose_equiv_classes(Classes,b=3):
    """
    Input: Classes = a list of representatives of equivalence classes of primitive IW matrices, one per each class. 
    b = depth of code invariant, used for efficiency.

    Output: A list of pairs of indices (i,j).

    It is assumed that the elements in 'Classes' are pairwise H-inequivalent. A pair (i,j) in the output list means that Classes[i] and Classes[j].transpose() are H-equivalent.
    """
    b=min(b,Classes[0].ncols())
    Codes=[nCount(A,b) for A in Classes]
    CodesT=[nCount(A.transpose(),b) for A in Classes]
    T_index_pairs=[]
    for i,C in enumerate(Codes):
        if test_equivalence(Classes[i],Classes[i].transpose(),b=b):
            continue
        for j,D in enumerate(CodesT):
            if C==D and i<=j:
                if test_equivalence(Classes[i],Classes[j].transpose(),b=b):
                    if i!=j:
                        T_index_pairs.append((i+1,j+1))
    return T_index_pairs
    



def classify_primitive_IW_old(n,w,b=4,d=1,exhaustive_list=False): ##This is the old implementation of the IW classification. Use classify_primitive_IW instead. 
    Classes=[]
    is_equiv_to_transpose=[]
    if not(exhaustive_list):
        Matrices=ExhaustiveListIW(n,w)
    else:    
        Matrices=exhaustive_list
    for A in Matrices:
        if not(is_primitive(A)):
            continue
        if not(A in Classes):
            new_class=True
            for B in Classes:
                if test_equivalence_old(A,B,b,d) or test_equivalence_old(A.transpose(),B,b,d):
                    new_class=False
                    break
            if new_class:
                Classes.append(A)
                if test_equivalence_old(A,A.transpose(),b,d):
                    is_equiv_to_transpose.append(True)
                else:
                    is_equiv_to_transpose.append(False)
    
    return  list(zip(Classes,is_equiv_to_transpose))


#### The following procedures are for proving that an automorphism subgroup is complete. #####

def orbits_single(G): ## G is given as a nxn monomial matrix group. The function returns the list of orbits of G as acting on the set {0,...,n-1}.
    """
    Input: A group of monomial matrices.
    Output: The list of orbits of the action of G on {0,...,n-1} (ignoring signs). Given as a list of sets.
    """
    I=G.an_element().matrix()
    n=I.nrows()
    X=list(range(n))
    Orbits=[]
    while len(X)>0:
        i=X[0]
        orbit=set()
        X.remove(i)
        for g in G:
            vj=g.matrix().column(i)
            vj=sum(vj)*vj
            j=tuple(vj).index(1)
            orbit.add(j)
            if j in X:
                X.remove(j)
        Orbits.append(orbit)
    return Orbits

def orbits(G,r):
    """
     Input: G = A group G of monomial matrices;
            r = a positive integer. 
    Output: The list of orbits of the action of G on {0,...,n-1}^r (ignoring signs), given as a list of sets.
    """
    if type(G)==list:
        G=MatrixGroup(G)
    I=G.an_element().matrix()
    n=I.nrows()
    X=set(range(n))
    #X=list(map(tuple,cartesian_product_iterator([X]*r)))
    X=list(map(tuple,Permutations(X,r)))
    Orbits=[]
    while len(X)>0:
        i=X[0]
        orbit=set()
        X.remove(i)
        for g in G:
            j=[]
            for xi in i:
                vj=g.matrix().column(xi)
                vj=sum(vj)*vj
                xj=tuple(vj).index(1)
                j.append(xj)
            tj=tuple(j)
            orbit.add(tj)
            if tj in X:
                X.remove(tj)
        Orbits.append(orbit)
    return Orbits

def stabilizer(G,v): ## G is given as a nxn monomial matrix group and v is a vector of length n. The function returns the stabilizer of v in G.
    """
    Input: G = A group G of nxnmonomial matrices;
            v = a vector of length n; 
    Output: The stabilizer in G of the vector v (ignoring signs in G).
    """
    Stab=[] ## Stab will be a list of generators of the stabilizer
    for g in G:
        in_stab=True
        for vi in v:
            j=g.matrix().column(vi)
            j=sum(j)*j
            vj=tuple(j).index(1)
            if vj!=vi: 
                in_stab=False
                break
        if in_stab:
            Stab.append(g.matrix())
    return Stab

def all_sign_mat(n):
    """
    Input: n = a positive integer.
    Output: A list of all n x n diagonal matrices with entries in {1,-1}.
    """ 
    H=HadamardSpace(n)
    return [-diagonal_matrix(h) for h in H]+[diagonal_matrix(h) for h in H]

def all_permutations(L1,L2):
    """
    Input: L1 and L2 are two lists of the same length.
    Output: All permutations pi such that pi(L1)=L2. If no such permutations exist, return False.
    """
    L1s=copy(L1)
    L2s=copy(L2)
    L1s.sort()
    L2s.sort()
    if L1s!=L2s:
        return False
    pi=perm_between(L1,L1s)
    sig=perm_between(L2s,L2)
    S=list(Set(L1s))
    S.sort()
    Pos=[]
    Groups=[]
    for x in S:
        Pos.append(L1s.index(x))
    Pos.append(len(L1))
    for i in range(len(Pos)-1):
        Groups.append(SymmetricGroup(domain=range(Pos[i]+1,Pos[i+1]+1)))
    L=[]
    siz=[]
    ln=0
    for Si in Groups:
        Li=list(Si)
        L.append(Li)
        siz.append(len(Li))
        ln+=Si.domain().cardinality()
    perms=[]
    Sn=SymmetricGroup(ln)
    for s in xmrange(siz):
        tau=Sn.identity()
        for i,ind in enumerate(s):
            tau=tau*L[i][ind]
        alpha=pi*tau*sig
        perms.append(alpha)
    return perms

def all_possible_isomorphisms_preserving_initial_up_to_signs(A,B,b,base=10):
    """
    Input: 
        A and B are two matrices of the same size, with the same first b rows. base is the base used for encoding vectors as integers.

    Output: 
        A list of all isomorphisms (L,R) such that L*A*R.transpose()==B, and L is diagonal in restriction to the first b coordinates.
    """
    H=HadamardSpace(b)
    Isoms=[]
    n=A.ncols()
    base_vec=vector([base^(n-1-i) for i in range(n)])
    NB,MB=NormalizeByColumns(B,base_vec,Mon=True)
    for S in H:
        D=diagonal_matrix(S+[1]*(A.nrows()-b))
        SA=D*A
        NA,MA=NormalizeByColumns(SA,base_vec,Mon=True)
        if NA[:b]!=NB[:b]:
            continue
        isoms1=all_possible_isomorphisms_preserving_initial(NA,NB,b,base)
        isoms=[(L*D,MB*R*MA.transpose()) for L,R in isoms1]
        Isoms.extend(isoms)
    return Isoms





def all_possible_isomorphisms_preserving_initial(A,B,b,base=10):
    """
    Given two matrices A and B of the same size, with the same first b rows, this function return all possible isomorphisms between A and B, which act as the identity on these first rows. In the realm of many repetitions of columns in A[:b]=B[:b], the function is cutting down the number of permutations by looking for isomorphisms between $A[b:,I]$ and $B[b:,I]$ for each group I of columns of A[:b] with the same column.

    Input: 
    
        A and B are two matrices of the same size, with the same first b rows. base is the base used for encoding vectors as integers.

    Output: A list of all isomorphisms (L,R) such that L*A*R.transpose()==B, and L is the identity in restriction to the first b coordinates.
    """
    n=A.nrows()
    m=A.ncols()
    base_vec=vector([base^(m-1-i) for i in range(m)])
    assert A[:b]==B[:b]
    ## We first find all occurrences of each column in A[:b].
    Occ=[]
    Cols=[]
    ii=-1
    zero=-1
    for col in A[:b].columns():
        if not(col in Cols):
            Cols.append(col)
            ii+=1
            if col==0:
                zero=ii
            occ=tuple([j for j in range(A.ncols()) if A[:b].column(j)==col])
            Occ.append(occ)
    ## Next we find all isomorphisms between A[b:,I] and B[b:,I].
    Perms={}
    #print(Occ)
    for ii,I in enumerate(Occ):
        Perms[I]=[]
        M=A[:b,I]; N=B[:b,I]
        Mc=A[b:,I]; Nc=B[b:,I]
        #print(I)
        SlI=SymmetricGroup(domain=range(len(I)))
        #SI=SymmetricGroup(domain=I)
        ## This block takes care of zero columns of A[:b], where we need to consider signed permutations.
        if ii==zero:
            for pi in SlI:
                for S in all_sign_mat(len(I)):
                    mon=pi.matrix()*S
                    #M1=M*pi.matrix()*S
                    M1c=Mc*mon
                    if NormalizeByColumns(M1c.transpose(),base_vec)==NormalizeByColumns(Nc.transpose(),base_vec):
                        #sigma=SI([I[pi(j)] for j in range(len(I))])
                        Perms[I].append(mon)
        ## If the columns are non-zero, we only need to consider permutations.
        else:
            for pi in SlI:
                mon=pi.matrix()
                #M1=M*mon
                M1c=Mc*mon
                if NormalizeByColumns(M1c.transpose(),base_vec)==NormalizeByColumns(Nc.transpose(),base_vec):
                    #sigma=SI([I[pi(j)] for j in range(len(I))])
                    Perms[I].append(mon)
        #print(f'Number of permutations this type: {len(Perms[I])}')
    Values=list(Perms.values())
    Isoms=[]
    NB=NormalizeByColumns(B.transpose(),base_vec)
    for combination in product(*Values):
        R=block_diagonal_matrix(combination).transpose()
        NA=NormalizeByColumns(R*A.transpose(),base_vec)
        if NB==NA:
            L=B*R*A.inverse()
            assert B==L*A*R.transpose()
            Isoms.append((L,R.transpose()))
    return Isoms
            



def minimal_fixed_row_element(A,base=10,permutations=False): #This returns the minimal matrix in the class of A, by the row lex ordering.
    """
    Input: A = an integer matrix; 

    base = 10: a positive integer serving as a base for the numerical encoding of integer vectors. 

    permutations = False (a boolean).

    Output: The minimal matrix in the class of A according to the row lex ordering. If permutations=True, also return the number of monomial matrices M such that M*A is column equivalent to the minimal matrix.
    """
    m=A.nrows(); n=A.ncols()
    Mon=all_sign_mat(m)
    CodeMin=n*[base^10]
    perms=0
    for M in Mon:
        MA=M*A
        MAnormC=NormalizeByColumns(MA,base)
        MAnormCode=list(MAnormC*vector([base^(n-j) for j in range(n)]))
        if MAnormCode==CodeMin:
            perms+=1
        if MAnormCode<CodeMin:
            perms=1
            CodeMin=MAnormCode
            MinMat=MAnormC
    if permutations:
        return MinMat,perms
    return MinMat

def perm_between(L1,L2):
    """
    Input: L1 and L2 are two lists of the same length.

    Output: a permutation pi such that pi(L1)=L2. If no such permutations exists return False.
    The function all_permutations(L1,L2) returns all such permutations. 
    """
    assert len(L1)==len(L2)
    if not( Counter(L1)==Counter(L2)):
        return False
    L2c=copy(L2)
    pil=[]
    for z in L1:
        j=L2c.index(z)
        pil.append(j+1)
        L2c[j]=''
    S=SymmetricGroup(len(L1))
    pi=S(pil)
    return(pi)

def find_L_from_R(A,R,base=10):
    """
    Input: 
    
           A = an integer matrix;

           R = a monomial matrix; 

           base = 10, a positive integer serving as a base for the numerical encoding of integer vectors.

    Output: Find a monomial R such that (L,R) is an automorphism of A, i.e. L*A*R.transpose()==A. If no such L exists, return False. R may not be unique.
    """
    
    n=A.nrows()
    AR=A*R.transpose()
    nA,sA=normAbove(A.transpose(),signs=True)
    nAR,sAR=normAbove(AR.transpose(),signs=True)
    cA=list(vector([base^(n-j) for j in range(n)])*nA)
    cAR=list(vector([base^(n-j) for j in range(n)])*nAR)
    pi=perm_between(cA,cAR)
    if not(pi):
        return False
    L=diagonal_matrix(sA)*pi.matrix()*diagonal_matrix(sAR)
    assert A==L*A*R.transpose()
    return L


def find_isomorphism_with_trivial_row_order(A,B,base=10): ### This is an old function and is not used any more.
    m=A.nrows()
    nB=NormalizeByColumns(B,base)
    mB,sB=normAbove(B,signs=True)
    LsB=[sB]
    if 0 in sB:
        I0=[i for s,i in enumerate(sB) if s==0]
        for t in xmrange(len(I0)*[2]):  #We try all possible sign changes in the zero columns.
            LsB=[]
            sBt=copy(sB)
            for i,ti in zip(I0,t):
                if ti==1:
                    sBt[i]=1
                else:
                    sBt[i]=-1
            LsB.append(sBt)

    cB=list(vector([base^(B.nrows()-j) for j in range(B.nrows())])*mB)
    Mon=all_sign_mat(m)
    Isoms=[]
    for M in Mon:
        MA=M*A
        nA=NormalizeByColumns(MA,base)
        if nA==nB:
            mA,sA=normAbove(MA,signs=True)
            cA=list(vector([base^(A.nrows()-j) for j in range(A.nrows())])*mA)
            for pi in all_permutations(cA,cB):
                for sB in LsB:
                    Isoms.append((M,diagonal_matrix(sA)*pi.matrix()*diagonal_matrix(sB)))
    return Isoms

def does_map(L,I,J): ### This is an old function and is not used any more.
    for ii,jj in zip(I,J):
        ci=L.column(ii)
        ci=sum(ci)*ci
        vj=tuple(ci).index(1)
        if vj!=jj: 
            return False
    return True
        

def test_if_I_maps_to_J(A,I,J,base=10):
    """
    Input: 
    
           A = an integer nxn matrix;

           I and J are two lists of the same length taken from the set {0, 1, ..., n-1}.

           base =10 is used for encoding vectors as integers.

    Output: If there exists an isomorphism (L,R) such that L*A*R.transpose()==A and L maps the rows in I to the rows in J, then return True, the number of such isomorphisms, and a list of these isomorphisms. Otherwise, return False.
    """
    B=A[I,:]
    C=A[J,:]
    BC=A.delete_rows(I)
    CC=A.delete_rows(J)
    if nCount(B,len(I))!=nCount(C,len(I)):
        return False
    Btot=B.stack(BC)
    Ctot=C.stack(CC)
    Isoms1=all_possible_isomorphisms_preserving_initial_up_to_signs(Btot,Ctot,len(I),base)
    if len(Isoms1)==0:
        return False
    P=matrix(Permutation([x+1 for x in I]+[x+1 for x in range(A.nrows()) if not(x in I)])).transpose()
    Q=matrix(Permutation([x+1 for x in J]+[x+1 for x in range(A.nrows()) if not(x in J)])).transpose()
    #assert P*A==Btot
    #assert Q*A==Ctot
    Isoms=[]
    for L,R in Isoms1:
        Isoms.append((Q.transpose()*L*P,R))
    return True,len(Isoms),Isoms

    
    


def test_if_I_maps_to_J_old(A,I,J,base=10): ### This is an old function and is not used any more. It is replaced by test_if_I_maps_to_J, which is more efficient.
    B=A[I,:]
    C=A[J,:]
    if nCount(B,3)!=nCount(C,3):
        return False
    BC=A.delete_rows(I)
    CC=A.delete_rows(J)
    if nCount(BC,3)!=nCount(CC,3):
        return False
    Isoms=find_isomorphism_with_trivial_row_order(B,C,base)
    if len(Isoms)==0:
        return False
    isom=0
    RIsom=[]
    LIsom=[]
    for L,R in Isoms:
        AR=A*R.transpose()
        X=AR.transpose()
        Y=A.transpose()
        nX=NormalizeByColumns(X,base)
        nY=NormalizeByColumns(Y,base)
        if nX==nY:
            LL=find_L_from_R(A,R,base)
            if does_map(LL,I,J):
                isom+=1
                RIsom.append(R)
                LIsom.append(LL)
    if isom>0:
        return True,isom,zip(LIsom,RIsom)
    else:
        return False
    
def prove_full_automorphism_group(A,G,base=10,orbs=3): #A is the IW and G is a subgroup of its automorphism group. The function returns True if G is the full automorphism group of A.
    #m=A.nrows()
    """
    This procedure proves or disproves that a given automorphism group is complete.

    Input: 
    
           A = an integer matrix; 

           G = a group of the automorphism group of A, given by its left side; 

           base = 10 is used for encoding vectors as integers; 

           orbs = an integer used internally in the program and can be set up to achieve more efficiency. The larger orbs is, the more time the procedure takes, but it finds faster a new automorphisms if there are any.

    Output: If G is the full automorphism group of A, return True. Otherwise, return a new automorphism L not in G.
    """
    orbs=min(orbs,A.nrows())
    Orbs=orbits(G,orbs)
    #for orb in Orbs:
    l0=list(Orbs[0])[0]
    t=test_if_I_maps_to_J(A,l0,l0,base)
    #if not(t):
    #    return False
    stab=stabilizer(G,l0)
    #print(t[1],len(stab))
    if 2*t[1]>len(stab):  ## The factor 2 is because we do not allow (-I,-I) in t[2].
        #print(t[1],len(t[2]),len(stab))
        #print('larger stabilizer')
        #print('The automorphism group is larger')
        for L,R in t[2]:
            if not(L in stab):
                #print('new automorphism found')
                return L
    s=len(Orbs)
    for j in range(1,s):
        #for j in range(i+1,s):
        I=list(Orbs[0])[0]
        J=list(Orbs[j])[0]
        t=test_if_I_maps_to_J(A,I,J)
        if t:
            #print('fusion')
            #print('The automorphism group is larger')
            #print(t)
            L,R=t[2][0]
            return L
    return True

#### The main procedure for computing the automorphism group of an IW matrix.

def automorphism_group(A,proof=True,base=10,ngens=6,orbs=3,algorithm=None,id=False):
    """
    Compute the automorphism group of an IW matrix A. The function returns a subgroup of the automorphism group, which is probably the full automorphism group, but this is not guaranteed. If proof=True, the function provably returns the full automorphism group. The output is given as a group of monomial matrices, given by their left side. To find the right counterpart of each left item L, use L=find_R_from_L(A,L).

        Input: 
        
               A = an integer matrix;

               proof=True: return provably the full automorphism group. If False, may return a proper subgroup. 

               base=10: is used for encoding vectors as integers.

               ngens=6: generate ngens random automorphisms. The larger ngens is, the more probable it returns the full group. 

               orbs=3: is used internally in the program and can be set up to achieve more efficiency in proving the completeness of the found group. 

               algorithm=None: if None, we use the Sage implementation of the graph isomorphism and automorphism problem. Algorithm='nauty' uses the external nauty package (if installed), which is much faster. In this case we do not use the option proof=True.

               id=False: if True, the function returns also a string which is a 'nauty' id of the Hadamard graph of A.

        Output: The automorphism group of A, given by its left projection. If id=True, also return the 'nauty' id of the Hadamard graph of A.
    
    
    """
    if algorithm=='nauty':
        if id:
            G,Id=automorphism_group_hadamard(A,id=True)
        else:
            G=automorphism_group_hadamard(A,id=id)
    else:
        G=approximate_automorphism_group(A,ngens=ngens)
    if not(proof) or algorithm=='nauty':
        if id and algorithm=='nauty':
            return G,Id
        else:
            return G
    GG=GL(A.nrows(),ZZ)
    while True:
        L=prove_full_automorphism_group(A,G,base=base,orbs=orbs)
        if type(L)==bool and L==True:
            return G
        gens=list(G.gens())+[GG(L)]
        G=GG.subgroup(gens)



def find_symmetric_and_and_antisymmetric_rep(A,b=3,Aut=False,ngens=5,All=False,base=10,proof=False,algorithm=None):
    """
    Find a symmetric and an antisymmetric matrix in the class of a matrix. Can also return exhaustive lists of both kinds. 

    Input: 
           
           A = an integer matrix;

           b = 3: depth of code invariant, used for efficiency;

           Aut = The automorphism group of A if it was computed. If Aut=False, compute internally the automorphism group.

           ngens,base,proof and algorithm: These parameters are used for computing the automorphism group if we set Aut=False. See automorphism_group for more details.

    Output: If All=False, return a pair (symA,anti_symA) of symmetric and antisymmetric matrices in the class of A. If one of which does not exist, return symA or anti_symA=False. If All=True, return a pair (AllSym,AllAntiSym) of exhaustive lists. Such a list may still contain SH-equivalent matrices.
    """
    T=test_equivalence(A,A.transpose(),b=b,algorithm=algorithm,certificate=True) ##TODO: Switch to graph isomorphism method.
    if not(T):
        raise ValueError('The class in not symmetric')
    L,R=T
    #R=R.transpose()
    assert L*A*R.transpose()==A.transpose()
    if not(Aut):
        Aut=automorphism_group(A,ngens=ngens,base=base,proof=proof)
    #print(f'Automorphism type : {Aut.cardinality()}')
    symA=False
    anti_symA=False
    AllSym=[]
    AllAntiSym=[]
    for sigmaL in Aut:
        sigmaR=find_R_from_L(A,sigmaL)
        S1=sigmaL*L.transpose()
        S2=sigmaR*R.transpose()
        if S1==S2.transpose():
            symA=S1.transpose()*A
            if All:
                AllSym.append((symA,S1.transpose()))
        elif S1==-S2.transpose():
            anti_symA=S1.transpose()*A
            assert anti_symA==-anti_symA.transpose()
            if All:
                AllAntiSym.append((anti_symA,S1.transpose()))
        if All:
            continue
        if symA and anti_symA:
            break
    if All:
        return AllSym,AllAntiSym
    return symA,anti_symA

def aut_sym(A,b=3,ngens=5,base=10,Aut=False):
    """
    Find the symmetric automorphism group of the matrix A. 

    Input: 
    
           A = an IW matrix.

           b = depth of code invariant, used for efficiency;

           base=10: is used for encoding vectors as integers. For entries in [-M,M] use base=2*M+1.

           Aut = The ordinary automorphism group. By default set to False and then computed by the procedure.

    Output: The monomial matrix group of symmetric automorphisms given by its left projection.

    """
    AutSym=[]
    if not(Aut):
        Aut=automorphism_group(A,ngens=ngens,base=base)
    #print(Aut.cardinality())
    for L in Aut:
        R=find_R_from_L(A,L)
        #assert L*A*R.transpose()==A
        if L.matrix()==R:
            #print('found sym aut')
            AutSym.append(L)
    if type(Aut)==list:
        Aut=MatrixGroup(Aut)
    return Aut.subgroup(AutSym)

def count_sym_and_antisym_matrices(A,b=3,Aut=False,ngens=5,base=10):
    """
    Count how many symmetric and antisymmetric matrices are in the H-equivalence class of A.

    Input: 

           A = an IW matrix.

           b = 3: the depth of code invariant, used for efficiency;

           base=10: is used for encoding vectors as integers. For entries in [-M,M] use base=2*M+1.

           Aut = False: The ordinary automorphism group. By default set to False and then computed by the procedure.

           ngens=5: Used in the course of computing the automorphism group and its value affects the efficiency.

    Output: A pair (ns,na) of integers that counts the number of symmetric and antisymmetric matrices.
    """
    if not(Aut):
        Aut=automorphism_group(A,ngens=ngens,base=base)
    n=A.nrows()
    SymA,AntiSymA=find_symmetric_and_and_antisymmetric_rep(A,b=b,Aut=Aut,ngens=ngens,All=True,base=base)
    O=[]
    ### Counting symmetric matrices ###
    for B,L in SymA:
        AutB=GL(n,ZZ).subgroup([L*g*L^-1 for g in Aut])
        H=aut_sym(B,b=b,base=base,Aut=AutB)
        #print(H)
        oB=Aut.cardinality()/H.cardinality()
        O.append(oB)
    SO=set(O)
    nsym=0
    for o in SO:
        no=O.count(o)/o
        nsym+=no/(Aut.cardinality()/o)
    nsym*=2^n*ZZ(n).factorial()

    ### Counting antisymmetric matrices ###
    nantisym=0
    if AntiSymA:
        O=[]
        for B,L in AntiSymA:
            AutB=GL(n,ZZ).subgroup([L*g*L^-1 for g in Aut])
            H=aut_sym(B,b=b,base=base,Aut=AutB)
            oB=Aut.cardinality()/H.cardinality()
            O.append(oB)
        SO=set(O)
        for o in SO:
            no=O.count(o)/o
            nantisym+=no/(Aut.cardinality()/o)
        nantisym*=2^n*ZZ(n).factorial()
    return nsym,nantisym


def classification_list_symm_and_antisymm(M,Aut=False,proof=True,algorithm=None):
    """
        Classify all symmetric and antisymmetric matrices up to symmetric equivalence in the H-equivalence class of an IW matrix M.

        Input:

            M = An IW matrix.

            Aut = False: The ordinary automorphism group. By default set to False and then computed by the procedure.

            proof = True: provably supply the answer when Aut = False, in which case the function is asked to compute a provably correct automorphism group.

            algorithm = None: Use the sage implementation for graph isomorphism functionality. If algorithm='nauty', use the 'natuy' package (if installed). In this option always proof=False.

        Output: A pair (Ls,La) of two lists. Ls is a classification list for symmetric matrices and La is a classification list for antisymmetric matrices.
    """
    if not(Aut):
        if algorithm=='nauty':
            GM=automorphism_group_hadamard(M)
        else:
            GM=automorphism_group(M)
    else:
        GM=Aut
    try: S,AS=find_symmetric_and_and_antisymmetric_rep(M,Aut=GM, All=True,algorithm=algorithm)
    except ValueError:
        return ([],[])
    SymClasses=[]
    ASymClasses=[]
    for i in range(len(S)):
        A,L=S[i]
        G=[L*g*L.transpose() for g in GM]
        SA=set()
        #print(f'{i=},len(sym)={len(SymClasses)}')
        for P in G:
            Q=find_R_from_L(A,P)
            M=Q.transpose()*P
            if M.transpose()*A*M.transpose()==A and M*A==(M*A).transpose():
                C=matrix(ZZ,M*A)
                #AutC=[GL(M.nrows(),ZZ)(M*g*M^-1) for g in GM]
                C.set_immutable()
                SA.add(C)
        if not(SA in SymClasses):
            SymClasses.append(copy(SA))
    SymReps=[list(SA)[0] for SA in SymClasses]
    for i in range(len(AS)):
        A,L=S[i]
        G=[L*g*L.transpose() for g in GM]
        SA=set()
        for P in G:
            Q=find_R_from_L(A,P)
            M=Q.transpose()*P
            if M.transpose()*A*M.transpose()==A and M*A==(M*A).transpose():
                C=matrix(ZZ,M*A)
                #AutC=[GL(M.nrows(),ZZ)(M*g*M^-1) for g in GM]
                C.set_immutable()
                SA.add(C)
        if not(SA in SymClasses):
            ASymClasses.append(copy(SA))
    
    ASymReps=[list(SA)[0] for SA in ASymClasses]
    return(SymReps,ASymReps)
        










###########  Main classification printing data ##############

def print_classification_data(n,w,b=3,base=10,Classes=False):
    """
    Print to the console the classification data of primitive IW(n,w). Also write the data to a text file named "Classification_n_w.txt".
    
    The data includes the following: 

        1) Number of H-equivalence classes.

        2) Of which Transpose H-equivalence pairs (index of).

        3) A table of automorphism groups (given by GAP id), generators, and the size of the class.

    Input: 
        n,w = The size and weight.

        b = 3: the depth of code invariant, used for efficiency;

        base=10: is used for encoding vectors as integers. For entries in [-M,M] use base=2*M+1.

        Classes = A classification list of primitive IW(n,w). If Classes=False (Default) compute the classification list internally.
    """
    fl=open(f'Classification_{n}_{w}.txt','w')
    if not(Classes):
        Classes=classify_primitive_IW(n,w,b)
    fl.write(f'There are {len(Classes)} primitive equivalence classes of order {n} and weight {w}.\n\n')
    print(f'Number of equivalence classes: {len(Classes)}')
    T_index_pairs=transpose_equiv_classes(Classes,b=b)
    for i,M in enumerate(Classes):
            fl.write(f'{i+1}\n')
            fl.write(f'{M}\n\n')

    fl.write(f'Transpose equivalence pairs: {T_index_pairs}\n\n')

    T_discard=[pair[1] for pair in T_index_pairs]
    T_keep=[pair[0] for pair in T_index_pairs]
    T_classes=[(i,M) for i,M in enumerate(Classes) if not(i+1 in T_discard)]
    total_prmitive=0
    fl.write('Serial number   |    Automorphism group type    |      Generators (L,R)    |   Size of class\n')
    fl.write('--------------------------------------------------------------------------------------------------\n')
    for i,M in T_classes:
        n=M.nrows()
        G=automorphism_group(M,b,d,proof=True,base=base)
        if hasattr(G,'id'):
            Gid=G.id()
        else:
            Gid=G.cardinality()
        gens=generating_set_of_automorphisms(M,G)
        class_size=(2^n*ZZ(n).factorial())^2/Gid[0]
        total_prmitive+=class_size
        if i+1 in T_keep:
            total_prmitive+=class_size
        fl.write(f'{i+1}     |      {Gid}       |'+ f'{f' {gens}   | {class_size}':{'>'}^{250}}' + '\n\n')
        print(f'{i+1}     |      {Gid}       |'+ f'{f' {gens}   | {class_size}':{'>'}^{250}}' + '\n\n')
    fl.write(f'Total number of primitive matrices of size {n} and weight {w} is: {total_prmitive}\n')
    fl.close()


def print_classification_data_json(n,w,b=3,base=10,Classes=False,max_entry=Infinity):
    """
    Generate a .json file of classification data of primitive IW(n,w) up to TH-equivalence. The output file will be "Classification_n_w.json", or "Classification_n_w_max_m.json" if the entries of the matrix are limited to the interval [-m,m]. 

    The json file will include the following fields:

    1) "Ordinal Number": The serial number of the class given by n.w.j where j in the serial number of the class, starting from j=1.

    2) "Matrix": The list of rows of the representing matrix of the class.

    3) "Automorphism Group": The automorphism group type of the class given by a GAP id (a pair of integers: [o,r] where o is the cardinality and r is the serial number in the GAP taxonomy).

    4) "Generators": A list of pairs (L,R) that generate to automorphism group. L and R are given by line codes of monomial matrices and are vectors of integers. 

    5) "Class Size": An integer which is the size of the class.

    And a final field  
    6) The total count of primitive IW(n,w).

    Input:
        n,w = The size and weight.

        b = 3: the depth of code invariant, used for efficiency;

        base=10: is used for encoding vectors as integers. For entries in [-M,M] use base=2*M+1.

        Classes = A classification list of primitive IW(n,w). If Classes=False (Default) compute the classification list internally.

        max_entry: Limit the entries of the matrix to be in the interval [-max_entry,max_entry].
    """
    import json
    def serialize_Integer(obj):
        if isinstance(obj, Integer) or isinstance(obj, Rational):
            return int(obj)
        raise TypeError(f"Type {type(obj)} is not serializable")

    if max_entry==Infinity:
        print(f'Classifying primitive matrices of size {n} and weight {w}')
        filename=f'Classification_{n}_{w}.json'
    else:   
        print(f'Classifying primitive matrices of size {n}, weight {w} and maximum entry = {max_entry}')
        filename=f'Classification_{n}_{w}_max_{max_entry}.json'
    if not(Classes):
        Classes=classify_primitive_IW(n,w,b=b,max_entry=max_entry)
    print(f'finished classification: There are {len(Classes)} primitive equivalence classes')
    if len(Classes)==0:
        print('No classes to analyze, exiting')
        return
    fl=open(filename,'w')
    T_index_pairs=transpose_equiv_classes(Classes,b=b)
    T_discard=[pair[1] for pair in T_index_pairs]
    T_keep=[pair[0] for pair in T_index_pairs]
    T_classes=[(i,M) for i,M in enumerate(Classes) if not(i+1 in T_discard)]
    print(f'There are {len(T_classes)} classes to analyze up to transpose equivalence')
    total_primitive=0

    json_lst=[]
    j=0
    for i,M in T_classes:
        j+=1
        print(f'Analyzing class number {i}')
        n=M.nrows()
        class_data={}
        G=automorphism_group(M,proof=True,base=base)
        if G.cardinality()<1000:
            Gid=G.id()
        else:
            Gid=[G.cardinality(),'']
        gens=generating_set_of_automorphisms(M,G)
        class_size=(2^n*ZZ(n).factorial())^2/Gid[0]
        total_primitive+=class_size
        symmetric_class=True
        if i+1 in T_keep:
            symmetric_class=False
        class_data["Ordinal Number"]=f'{n}.{w}.{j}'
        class_data["Matrix"]=[list(row) for row in M.rows()]
        class_data["Automorphism Group"]=Gid
        class_data["Generators"]=gens
        class_data["Equivalent to its Transpose"]=symmetric_class
        class_data["Class Size"]=class_size
        json_lst.append(class_data)
        if i+1 in T_keep:
            total_primitive+=class_size
    json_lst.append({f"Total number of primitive matrices of size {n}, and weight {w} is": total_primitive})
    json.dump(json_lst,fl,default=serialize_Integer,indent=4)
    #fl.write(f'Total number of primitive matrices of size {n} and weight {w} is: {total_primitive}\n')
    fl.close()
                     