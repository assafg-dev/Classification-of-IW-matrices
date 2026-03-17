load('BackTracking3.sage')
load('PermsBetweenMatrices.sage')
load('Classification.sage')
load('automorphisms_via_graphs.sage')

from itertools import product

def read_permutation_group(s):
    l=s.split('),')
    l=[x+')' for x in l[:-1]]+[l[-1]]
    return PermutationGroup(l)

### This function computes a subgroup of the automorphism group of an IW A. This is done by randomly generating automorphisms. The result is probably the full automorphism group, but this is not guaranteed.
def approximate_automorphism_group(A,ngens=6):
    """ 
    Compute a subgroup of automorphisms of A by randomly adjoining ngens elements.
        The result is probably the full automorphism group, but this is not guaranteed.
    """
    #b=min(b,A.ncols())
    n=A.nrows()
    In=identity_matrix(ZZ,n)
    Aut=[-In] # This is always an automorphism.
    GeM=extended_automorphism_group(A)
    for _ in range(ngens):
        LR=an_automorphism(A,ExtAut=GeM) # Compute an automorphism of A (left and right side).
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
    H=G.as_permutation_group()
    gensH=H.minimal_generating_set()
    phi=H.hom(G)
    return list(map(phi,gensH))

def mon_to_sign_perm(N):
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
    L1=L
    if hasattr(L,'matrix'):
        L1=L.matrix()
    R=find_L_from_R(A.transpose(),L1.transpose(),base).transpose()
    return R

def generating_set_of_automorphisms(A,G):
    min_gens=min_gen_set(G)
    Rights=[find_R_from_L(A,LL) for LL in min_gens]
    return [(mon_to_sign_perm(LL),mon_to_sign_perm(RR)) for LL,RR in zip(min_gens,Rights)]
        

#### Here we classify the IW matrices up to equivalence. ####

def is_primitive(A):
    n=A.nrows()
    Gr=DiGraph(A)
    return Gr.is_connected()

def test_equivalence_old(A,B,b=4,d=1):
    try:
        equiv=Are_Equivalent(A,B,b,d)
    except ValueError:
        equiv=Are_Equivalent(A,B,b,d+1)
    if equiv:
        return equiv
    return False

def test_equivalence(A,B,b=3):
    isom=an_isomorphism(A,B)
    if isom:
        return isom
    elif nCount(A,b)!=nCount(B,b):
        return False

def classify_by_code(Matrices,b=4):
    code_classes={}
    for A in Matrices:
        if is_primitive(A):
            codeA=nCount(A,b)
            code_classes.setdefault(tuple(codeA),[]).append(A)
    return code_classes

def classify_primitive_IW(n,w,b=3,exhaustive_list=False, max_entry=Infinity):
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
    



def classify_primitive_IW_old(n,w,b=4,d=1,exhaustive_list=False):
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


#### From here below we are working on proving that we have the full automorphism group. #####

def orbits_single(G): ## G is given as a nxn monomial matrix group. The function returns the list of orbits of G as acting on the set {0,...,n-1}.
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

def orbits(G,r): ## G is given as a nxn monomial matrix group. The function returns the list of orbits of G as acting on the set {0,...,n-1}^r.
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

def all_sign_mat(n): #This gives the full list of all signature matrices up to order n.
    H=HadamardSpace(n)
    return [-diagonal_matrix(h) for h in H]+[diagonal_matrix(h) for h in H]

def all_permutations(L1,L2):
    """
    Given two lists L1 and L2 of the same length, this function returns all permutations pi such that pi(L1)=L2, if such permutations exist. Otherwise it returns False.
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
    assert len(L1)==len(L2)
    if not( set(L1)==set(L2)):
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


def find_isomorphism_with_trivial_row_order(A,B,base=10):
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

def does_map(L,I,J):
    for ii,jj in zip(I,J):
        ci=L.column(ii)
        ci=sum(ci)*ci
        vj=tuple(ci).index(1)
        if vj!=jj: 
            return False
    return True
        

def test_if_I_maps_to_J(A,I,J,base=10):
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

    
    


def test_if_I_maps_to_J_old(A,I,J,base=10):
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
            print('fusion')
            #print('The automorphism group is larger')
            #print(t)
            L,R=t[2][0]
            return L
    return True

def automorphism_group(A,proof=True,base=10,ngens=6,orbs=3,algorithm=None):
    if algorithm=='nauty':
        G=automorphism_group_hadamard(A)
    else:
        G=approximate_automorphism_group(A,ngens=ngens)
    if not(proof):
        return G
    GG=GL(A.nrows(),ZZ)
    while True:
        L=prove_full_automorphism_group(A,G,base=base,orbs=orbs)
        if type(L)==bool and L==True:
            return G
        gens=list(G.gens())+[GG(L)]
        G=GG.subgroup(gens)



def find_symmetric_and_and_antisymmetric_rep(A,b=3,Aut=False,ngens=5,All=False,base=10,proof=False):
    T=test_equivalence(A,A.transpose(),b=b) ##TODO: Switch to graph isomorphism method.
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


def classification_list_symm_and_antisymm(M,Aut=False):
    if not(Aut):
        GM=automorphism_group(M)
    else:
        GM=Aut
    try: S,AS=find_symmetric_and_and_antisymmetric_rep(M,All=True)
    except ValueError:
        return ([],[])
    SymClasses=[]
    ASymClasses=[]
    for i in range(len(S)):
        A,L=S[i]
        G=[L*g*L.transpose() for g in GM]
        SA=set()
        print(f'{i=},len(sym)={len(SymClasses)}')
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
        #fl.write(f'{i+1}     |      {Gid}       |'+ f'{f' {gens}   | {class_size}':{'>'}^{250}}' + '\n\n')
        #print(f'{i+1}     |      {Gid}       |'+ f'{f' {gens}   | {class_size}':{'>'}^{250}}' + '\n\n')
    fl.write(f'Total number of primitive matrices of size {n} and weight {w} is: {total_prmitive}\n')
    fl.close()


def print_classification_data_json(n,w,b=3,base=10,Classes=False,max_entry=Infinity):
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
                     