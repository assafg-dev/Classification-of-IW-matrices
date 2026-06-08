tri=vector([1,3,9,27,81,243])


def color(row0,vec):   ### Color a 0,1-vector 'row0' with a color vector 'vec'.
        one=0
        row=copy(row0)
        for j in range(len(list(row0))):
            if row[j]!=0:
               row[j]=vec[one]
               one+=1
        return row
  
def Colorings(v):  ### Output a list of all colorings of 'v', normalized to 1 on the first nonzero coordinate.
    Colorings=[]
    n=sum(v)
    for m in xmrange((n-1)*[2]):
        col=[1]+[2*z-1 for z in m]
        Colorings.append(color(v,col))
    return Colorings
   
def Bins(n,k): ### Generate all binary n-vectors of weight k.
    b=k*[1]+(n-k)*[0]
    P=Permutations(b)
    return map(vector,P.list())
    
def WeiVecs(n,k):  ### Output all weighing vectors of lenght n and weight k.
    Wei=[]
    B=Bins(n,k)
    for b in B:
        Wei+=Colorings(b)
    return Wei

def SecondRow(n,k):  ### Output all 2nd (n,k) rows given the *standard* 1st row.
    Wv=WeiVecs(n,k)
    Cand=[]
    t=matrix(k*[1]+(n-k)*[0])
    for w in Wv:
        if t*w==0:
            Cand.append(w)
    return Cand


def perm_between(L1,L2):
    assert len(L1)==len(L2)
    if not( Set(L1)==Set(L2)):
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
        


def PermMat(pi,n):
    I=identity_matrix(n)
    I.permute_rows(pi)
    
    return I
    
def Cols2Mult(M,tri,perm=False):   ## Given a partial weighing matrix M, return a unique code for its *column* Hadamard equivalence class. 
    A=copy(M)
    n=A.nrows()
    r=A.ncols()
    C=[[A[i,j] for i in range(n)] for j in range(r)]
    Code=[]
    Signs=[]
    for i in range(r):
        c=C[i]
        e=list(map(abs,c))
        if max(e)>0:
            t=0
            while e[t]==0:
               t+=1
            A.rescale_col(i,sign(c[t]))    ##### changed c[t] to sign(c[t])
            Signs.append(c[t])
        else:
            Signs.append(1)
    Code=list(tri*A)
    
    
    if perm:
        S=SymmetricGroup(r)
        Code1=copy(Code)
        Code.sort()
        pi=perm_between(Code,Code1)
        return Code,S(pi),Signs
    Code.sort()
    return Code

def SignMult(M,s): ##C# Multiply the *rows* of the matrix M by a signature vector 's'.
    Ms=copy(M)
    n=Ms.nrows()
    for i in range(n):
        Ms.rescale_row(i,s[i])
    return Ms

def SignMultCol(M,s):
    Ms=copy(M)
    n=Ms.nrows()
    for i in range(n):
        Ms.rescale_col(i,s[i])
    return Ms	

def PermCode(M,tri,perm=False,Signs=True):  ### This is similar to the above
    Codes=[]
    n=M.nrows()
    P=SymmetricGroup(n)
    PL=P.list()
    if Signs:
    	S=Colorings(n*[1])
    else:
        S=[n*[1]]
    Z=[]
    for l in range(len(S)):
        s=S[l]
        Ms=SignMult(M,s)
        for k in range(len(PL)):   
            pi = PL[k] 
            Mp=copy(Ms)
            Mp.permute_rows(pi)            
            Code=Cols2Mult(Mp,tri)
            Codes.append(tuple(Code))
            Z.append((k,l))
    if perm:
        mcode=min(Codes)
        nCodes=Codes.count(mcode)
        mCodes=[]
        for ii in range(nCodes):
                ind=Codes.index(mcode)
                k,l=Z[ind]
                Codes[ind]=''
                mCodes.append((mcode,P[k],S[l]))
        return mCodes
    else:
    	Codes.sort()
        
    	return Codes[0]

    
def ModHad(T,counts=False):  ### This returns a sublist S of the given T with a unique representative modulo *column* Hadamard Equivalence. If counts=True, then return the frequency vector of each representative.
    Codes=[]
    S=[]
    FCodes=[]
    Freq=[]
    for t in T:
        Cd=Cols2Mult(t,tri[:t.nrows()])
        FCodes.append(Cd)
        if not(Cd in Codes):
            Codes.append(Cd)
            S.append(t)
    for Cd in Codes:
        Freq.append(FCodes.count(Cd))
    if counts:
        return S,Freq
    else:
    	return S

def add_and_normalize(T,Wv,counts=False): ### Given a list T of partial weighing matrix and a list 'Wv' of weighing vectors, return a list of representatives for the *column* Hadamard equivalence classes of all elements of T augmented by all elements of Wv. If counts=True, also return a frequency vector of each item.
    T1fat=[]
    for t in T:
        for w in Wv:
            if t*w==0:
                T1fat.append(matrix(t).stack(w))
    T1=ModHad(T1fat,counts=counts)
    return T1


def Permute(M,pi):  ### Permute the *rows* of the matrix M according to the permutation 'pi'.
    Mp=M[[pi(j+1)-1 for j in range(M.nrows())]]
    return Mp




def ModPerms(T):
    Codes=[]
    S=[]
    for t in T:
        Cd=PermCode(t,tri[:t.nrows()])
        if not(Cd in Codes):
            Codes.append(Cd)
            S.append(t)
    return S

    

def BackTracking(Minit,Cand,depth,n):
    Minit=Minit[:depth]
    #M=matrix(Minit)
    ind=-1
    if depth>Min:
        c=Minit[-1]
        ind=Cand.index(c)
    NewCand=[d for d in Cand[ind+1:] if Minit*d==0]
    count=0
    for d in NewCand:
	    
            if depth==Min:
                count+=1
            Mnew=Minit.stack(d)
	
            if depth==n-1:
                Matrices.append(Mnew)
            if depth<n-1:  
                 
                BackTracking(Mnew,NewCand,depth+1,n)
    if depth==n-1 or depth<Min:
        return 
    
def CreateInit(M,Cand,depth):
    global INITS,Max
    NewCand=[d for d in Cand if M*d==0]
    Inits=[]
    for d in NewCand:
        Md=M.stack(d)
        Inits.append(Md)
    Inits=ModHad(Inits)
    Inits=ModPerms(Inits)
    if depth==Max:
        INITS+=Inits
        return
    for M1 in Inits:
        CreateInit(M1,NewCand,depth+1)
    return

def AllInitials(n,k,Width):
    global INITS,Max
    INITS=[]
    Cands=SecondRow(n,k)
    Max=Width-1
    CreateInit(matrix(k*[1]+(n-k)*[0]),Cands,1)
    INITS=ModPerms(INITS)
    return INITS

def StabC(R):
    m,n=R.parent().dims()
    C=Cols2Mult(R,tri[:R.nrows()])
    S=Set(C)
    stab=1
    for s in S:
        stab*=ZZ(C.count(s)).factorial()
        if s==0:
            stab*=2^C.count(s)
    return stab

def Orb(M):  
    Codes=[]
    n=M.nrows()
    m=M.ncols()
    P=Permutations(n)
    S=Colorings(n*[1])
    for pi in P:
        for s in S:
            Mp=Permute(M,pi)
            Ms=SignMult(Mp,s)
            Code=Cols2Mult(Ms,tri[:Ms.nrows()])
            Codes.append(tuple(Code))
    Codes.sort()
    return 2^(m+n)*ZZ(m).factorial()*ZZ(n).factorial()/(Codes.count(Codes[0])*StabC(M))

def Complete(INITS,Wv,n):
    global Min,Matrices
    Nmats=[]
    Min=INITS[0].nrows()
    Matrices=[]
    l0=0
    T=INITS
    for j in range(len(T)):
        Cands=[]
        M=T[j]
        for w in Wv:
            if M*w==0:
                Cands.append(w)
        #print("there are %s candidates for 5th row"%len(Cands))
        if len(Cands)<=300:
            #return M,Cands,Min,n
            
            BackTracking(M,Cands,Min,n)
            l1=len(Matrices)
            Nmats.append((j,l1-l0))
            
            l0=copy(l1)
        else:
            T1,F=add_and_normalize([T[j]],Cands,counts=True)
            
            #print("found %d normalizations"%len(T1))
            l1=copy(l0)
            nmats=0
            for k in range(len(T1)):
                Cands1=[]
                M=T1[k]
                for w in Cands:
                    if M*w==0:
                        Cands1.append(w)
                BackTracking(M,Cands,Min+1,n)
                delta=len(Matrices)-l1
                l1=len(Matrices)
                nmats+=delta*F[k]
            l0=copy(l1)
           # nmats=nmats/(n-4)
            Nmats.append((j,nmats))

        #print("finished backtracking case %s"%j)
        #print("added %s new matrices"%Nmats[j][1])
        
    return Nmats,Matrices

def CountWMats(INITS,Nmats,n):
    s=0
    w=INITS[0].nrows()
    for j in range(len(INITS)):
        s+=Orb(INITS[j])*Nmats[j][1]*2^(n-w)*ZZ(n-w).factorial()
    return s/2  ### (Why is this 2?  Understood!)



def geom(M):
    G=copy(M)
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            if M[i,j]==-1:  G[i,j]=1
    return G



def nCount(M,r,findtype=False,Signs=True):
    global Codes,R,positions
    R=r
    Codes=[]
    positions=[]
    iterCodes(M,r,[],findtype=findtype,Signs=Signs)
    if findtype:
       return positions
    S=set(Codes)
    Counts=[]
    for s in S:
        Counts.append((s,Codes.count(s)))
    Counts.sort()
    return Counts

def iterCodes(M,r,I,findtype=False,Signs=True):
    if r>0:
       if len(I)==0: 
          t=-1
       else:
          t=I[-1]
       for k in range(t+1,M.nrows()):
           Ik=I+[k]
       	   iterCodes(M,r-1,Ik,findtype=findtype,Signs=Signs)
    else:
       three=M[I]
       Code = PermCode(three,tri[:R],Signs=Signs)
       if findtype==Code:
          positions.append(I)
          return
       Codes.append(Code)
       return

def ThreeCount(M):
    Codes=[]
    n=M.nrows()
    for i in xrange(n):
        for j in xrange(i+1,n):
            for k in xrange(j+1,n):
                three=M[[i,j,k]]
                Code = PermCode(three,tri)
                Codes.append(Code)
    S=Set(Codes)
    Counts=[]
    for s in S:
        Counts.append((s,Codes.count(s)))
    Counts.sort()
    return Counts

def FourCount(M):
    Codes=[]
    n=M.nrows()
    for i in xrange(n):
        for j in xrange(i+1,n):
            for k in xrange(j+1,n):
                for l in xrange(k+1,n):
                    four=M[[i,j,k,l]]
                    Code = PermCode(four,tri)
                    Codes.append(Code)
    S=Set(Codes)
    Counts=[]
    for s in S:
        Counts.append((s,Codes.count(s)))
    Counts.sort()
    return Counts

def GeomCount(M):
    G=geom(M)
    Gram=G*G.transpose()
    G1=(Gram).list()
    G2=(G.transpose()*G).list()
    char=(Gram.charpoly(),)
    for r in [0,2,4,6]:
        char+=(G1.count(r),G2.count(r))
    return char

def GeomChar(M):
    G=geom(M)
    Gram1=G*G.transpose()
    Gram2=G.transpose()*G
    l1=Gram1.rows()
    l2=Gram2.rows()
    char=(Gram1.charpoly(),)
    counts1=[tuple([list(r1).count(r) for r in [0,2,4,6,8,9]])  for r1 in l1 ]
    counts2=[tuple([list(r1).count(r) for r in [0,2,4,6,8,9]])  for r1 in l2 ]
    counts1.sort()
    counts2.sort()
    char+=(counts1,counts2)
    return char


def FindType(M,Tcode):
    Codes=[]
    TCodes=[]
    n=M.nrows()
    for i in xrange(n):
        for j in xrange(i+1,n):
            for k in xrange(j+1,n):
                three=M[[i,j,k]]
                Code = PermCode(three,tri)
                Codes.append(Code)
                if Code==Tcode:
                    TCodes.append([i,j,k])
    return TCodes

def bring_to_front(M,Type,nloc,b,perm=False,Signs=True):
    locations=nCount(M,b,findtype=Type,Signs=Signs)
    assert nloc<len(locations)
    #print("locations=",locations)
    M1=copy(M)
    loc=locations[nloc]
    m=M.nrows()
    S=SymmetricGroup(m)
    
    pi=S([x+1 for x in loc]+[i+1 for i in range(m) if not(i in loc)])
    M1.permute_rows(pi)
    Ms=[]
    
    for Code,pi2,s2 in PermCode(M1[list(range(b))],tri[:b],perm=True,Signs=Signs):
        M11=copy(M1)
        s2=s2+(m-len(s2))*[1]
        M11=SignMult(M11,s2)
        M11.permute_rows(pi2)
        Code3,pi3,s3=Cols2Mult(M11[list(range(b))],tri[:b],perm=True)
        M11=SignMultCol(M11,s3)
        M11.permute_columns(pi3)
        if perm:
            PiRows=PermMat(pi2,m)*diagonal_matrix(s2)*PermMat(pi,m)
            PiCols=diagonal_matrix(s3)*PermMat(pi3,M.ncols())^-1
            Ms.append((M11,PiRows,PiCols))
            #print(PiRows*M*PiCols==M11)
        else:  
            Ms.append(M11)
    return Ms

def normalize_rows(M,start,signs=False):
    M1=copy(M)
    Signs=start*[1]
    for i in range(start,M1.nrows()):
        row=M1.row(i)
        e=list(map(abs,row))
        if 1 in e:
            t=e.index(1)
            M1.rescale_row(i,row[t])
            Signs.append(row[t])
        else:
            Signs.append(1)
    if signs:
        S=diagonal_matrix(Signs)
        #print(M1==S*M)
        return M1,S
    else:
        return M1

import itertools

def menaya1(M,b,d):
    #print M
    m,n=M.parent().dims()
    Sn=SymmetricGroup(n)
    Top=M[:b]
    Code=tuple(tri[:b]*Top)
    S=Set(Code)
    S=list(S)
    S.sort()
    #print(f'{S=}')
    minx=[]
   
    ### Find the starting position of each x in Code.
    for x in S:
        #print (x,S.index(x))
        minx.append(S.index(x))
    mind=[i for i in minx if i<=d]    ## Filter only those less than d.
    PermGroups=[]   ## A list of symmetric groups for permuting the columns
    for i in range(len(mind)-1):
        Si=SymmetricGroup(range(1+minx[i],1+minx[i+1]))
        PermGroups.append(Si)
   
    i=len(mind)-1  ### Create all partial sets of appropriate size to fill up the rightmost part of Code.
    if len(minx)<i+2:
       r=Top.ncols()
    else:
       r=minx[i+1]
    L=range(minx[i],r)
    #print(f'{Code=}, {L=}, {d=}, {minx=}, {i=}')
    S1=Set(L)
    Subs=S1.subsets(size=d-minx[i])
    Subs=[list(s1) for s1 in Subs]
    Signs=[len(Code)*[1]]
    if 0 in S:    ### If some columns are 0, add a sign group Signs
        min0=Code.index(0)
        if Code[-1]==0:
            max0=len(Code)
        else:
            i1=minx.index(min0)
            max0=minx[i1+1]
        Signs=[]
        for c in mrange((max0-min0)*[2]):
            sign=min0*[1]+[2*t-1 for t in c]+(len(Code)-max0)*[1]
            Signs.append(sign)

  
    Mlist=[]
    mx=minx[i]
    for g in itertools.product(*PermGroups):
        
        for s1 in Subs:
            M0=copy(M)
            s2=s1+[y for y in range(mx,Top.ncols()) if not(y in s1)]
            Isig=identity_matrix(M0.ncols())
            Isig[:,mx:]=Isig[:,s2]
            M0[:,mx:]=M[:,s2]
            
            for pi in g:
                Ipi=identity_matrix(M0.ncols())
                M1=copy(M0)
                Ipi.permute_columns(pi)
                M1.permute_columns(pi)
                #print(M0*Ipi==M1)
                for s in Signs:
                    Ms=SignMultCol(M1,s)
                        
                    Ms,S=normalize_rows(Ms,b,signs=True)
                    
                    Side=Ms[:,:d]
                    signvec=b*[1]
                    for i in range(b,M.nrows()):
                        if Side.row(i)==0:
                            signvec.append(2)
                        else:
                            signvec.append(1)
                    for c in mrange(signvec):
                        s1=[1-2*t for t in c]
                        Mc=SignMult(Ms,s1)
                        #print(diagonal_matrix(s1)*S*M*(Isig*Ipi*diagonal_matrix(s))==Mc)
                        Mlist.append((Mc,diagonal_matrix(s1)*S,Isig*Ipi*diagonal_matrix(s)))
                        

    return Mlist

def menaya(M,b,d):#_for_hadamard(M):  #### This is for Hadamard matrices. 
    n=M.nrows()
    Sn=SymmetricGroup(n)
    Mlist=[]
    for i in range(n):
        for j in range(n):
           M1=copy(M)
           pi=Sn([i+1]+list(range(1,i+1))+list(range(i+2,n+1)))
           sig=Sn([j+1]+list(range(1,j+1))+list(range(j+2,n+1)))
           M1.permute_rows_and_columns(pi,sig)
           sr=M1.column(0)
           sc=M1.row(0); sc[0]=1   
           M1=SignMult(M1,sr)
           M1=SignMultCol(M1,sc)
        Mlist.append((M1,diagonal_matrix(sr)*PermMat(pi,n),PermMat(sig,n)*diagonal_matrix(sc)))
    return Mlist
        

ff1 = lambda x: floor(10*sin(x))-1
ff2 = lambda x: x*abs(x+1)
ff3 = lambda x: x^2/(x-3)
ff4 = lambda x: x*sin(x)
ff5 = lambda x: floor(100*cos(100*x))

def apply(ff,M):
    U=copy(M)
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            U[i,j]=ff(M[i,j])
    return U

def Apply(FF,M0):
    M=matrix(QQ,M0)
    for f in FF[:-1]:
       
    	M=apply(f,M)^-1
    M5=apply(FF[-1],M)
    return M5
    
def TestCharPoly(LM,P):
    GoodLM=[]
    c=0
    #print('|LM|=',len(LM))
    for M,A1,A2 in LM:
        #t={-1:3,0:1,1:7}
        U=apply(ff1,M)
        G=U*U.transpose()
        Q=G.charpoly()
	#print "Q=",Q
        c+=1
        if vector((P-Q).coefficients()).norm()<1e-4:
            GoodLM.append((M,A1,A2))
        if c%500==0:
           #print(len(GoodLM))
           return GoodLM
    return GoodLM

Round=lambda r:round(10^6*r.real())


def Are_Equivalent(M1,M2,b,d,perm=True):
    Th1=nCount(M1,b)
    Th2=nCount(M2,b)
    if Th1!=Th2:
        return False
    #m=min([t[1] for t in Th1])
    mzcount=min([t[0].count(0) for t in Th1])
    Code=[t[0] for t in Th1 if t[0].count(0)==mzcount][0]
    for t in Th1:
        if t[0]==Code:
            m=t[1]
            break
    #Code=[t[0] for t in Th1 if t[1]==m][0]
    #print(Code)
    M11,La,Ra=bring_to_front(M1,Code,0,b,perm=perm)[0]
    M111,S=normalize_rows(M11,b,signs=True)
    U=Apply([ff1],M111)
    G=U*U.transpose()
    P=G.charpoly()
    #print("m=",m)
    Good=[]
    MoreInfo=[]
    for i in range(m):
        bf=bring_to_front(M2,Code,i,b,perm=perm)
        for M22,Lb,Rb in bf:
            M222,S2=normalize_rows(M22,b,signs=True)
            LM=menaya1(M222,b,d) #For Hadamard use, use menaya.
            TCP=TestCharPoly(LM,P)
            Good+=TCP
            MoreInfo+=len(TCP)*[(Lb,Rb,S2)]
    print("len(Good)=",len(Good))
    if Good!=[]:  ### Then probably the matrices are equivalent by pure permutations (no signs)
        ng=len(Good)
        Sn=SymmetricGroup(ng)
        pi=Sn.random_element()
        Good=[Good[pi(i+1)-1] for i in range(ng)]
        MoreInfo=[MoreInfo[pi(i+1)-1] for i in range(ng)]
        for ii in range(len(Good)):
            M3,Lc,Rc = Good[ii]
            Lb,Rb,S2 = MoreInfo[ii]
                    ###### ***** print Lc*M222*Rc==M3
            #save(M111,'/media/sf_Dropbox/Assaf/W1.sobj')
                    #save(M3,'/media/sf_Dropbox/Assaf/W2.sobj')
            perms=find_perms(M111,M3)  ### Add find perms
            #print("perms=",perms)
            if perms[0]:
                    sigc,sigr=perms
                    Ic=identity_matrix(M111.nrows())
                    Ir=copy(Ic)
                    Ic.permute_rows(sigc)
                    Ld=Ic
                    Ir.permute_columns(sigr)
                    Rd=Ir
                    #print(Ld*M3*Rd==M111)

                    return (Lc*S2*Lb)^-1*Ld*S*La,Ra*Rd*(Rb*Rc)^-1
    
    return False


def find_perms(M1,M2):   ### find equivalence permutations (when signs are not involved)
    #print('find perms')
   # t={-1:3,0:1,1:7}
    U1=Apply([ff1],M1)
    U2=Apply([ff1],M2)
    G1=U1.transpose()*U1
    G2=U2.transpose()*U2
    
    #sigr=eigenvector_similarity1(G1,G2)
    #sigr=FindPerm(G1,G2)
    LSig=FindManyPerms(G1,G2,tol=1)
    #PG2.permute_rows_and_columns(sigr^-1,sigr^-1)
    for sigr in LSig: 
        #save(M1,'/media/sf_Dropbox/Assaf/M1.sobj')
        #save(M2,'/media/sf_Dropbox/Assaf/M2.sobj')
        #print("sigr=",sigr)
        M2p=copy(M2)
        M2p.permute_columns(sigr^-1)
        R1=list(map(str,M1.rows()))
        R2=list(map(str,M2p.rows()))
        sigc=perm_between(R2,R1)
 


        if sigc:
            #print("sigc=",sigc)
            M2per=copy(M2)
            M2per.permute_rows_and_columns(sigc^-1,sigr^-1)
            if M2per==M1:
                #print("good")
                return sigc,sigr

    return False,False

def dilul(Mag,INITDATA=False):
    MinW=[]
    if INITDATA:
        NMats,INITS=INITDATA
        count=0
        for i in range(len(NMats)):
            nm=NMats[i][1]
            Cd=PermCode(INITS[i],tri)
        for _ in range(nm):
            W=Mag[count]
            if IsMinimal(W,10,Code=Cd):
                MinW.append(W)
            count+=1
        return MinW
    else:
        for W in Mag:
            if IsMinimal(W,10):
                MinW.append(W)
        return MinW

def rand_elt(S):
    m=len(S)
    return S[randrange(m)]

def rand_subset(n,w):
    S=range(n)
    Sub=[]
    for i1 in range(w):

        i=rand_elt(S[:-(w-i1)])
        j=S.index(i)
        S=S[j+1:]
        Sub.append(i)
    return Sub

def IsMinimal(M,ntry,Code=False):
    tri=vector([1,3,9,27])
    C=PermCode(M[:4],tri)
    if Code:
       C=Code
    for _ in range(ntry):
        sub=rand_subset(M.nrows(),4)
        N=M[sub,:]
        CN=PermCode(N,tri)
        if CN<C:
            return False
    return True


    
def gen_aut(W,b,d):
    n=W.nrows()
    S=SymmetricGroup(n)
    pi=S.random_element()
    sig=S.random_element()
   # W2=copy(W)
    L2=PermMat(pi,n)
    R2=PermMat(sig,n)
    S2=diagonal_matrix([2*randrange(2)-1 for u in range(n)])
    T2=diagonal_matrix([2*randrange(2)-1 for u in range(n)])
    S2=L2=identity_matrix(n)
    #S2=T2=identity_matrix(n)
    W2=S2*L2*W*R2*T2
    LR=Are_Equivalent(W2,W,b,d)
    if not(LR):
        return False
    L,R=LR
    if L*W2*R==W:
        return L*S2*L2,R2*T2*R

def orbit(P,Auts,n):
    i,j=P
    M=matrix(n)
    
    maslul=[(i,j)]
    
    for L,R in Auts:
        M[i,j]=1
        M=L*M*R.transpose()
        for i1 in range(n):
            for j1 in range(n):
                if M[i1,j1]!=0:
                    maslul.append((i1,j1))
    return Set(maslul)
 
def all_orbits(Auts,n):
    Orbs=[]
    covered=()
    for i in range(n):
        for j in range(n):
            P=(i,j)
            if not(P in covered):
                maslul=tuple(orbit(P,Auts,n))
                covered+=maslul
                Orbs.append(maslul)
    return Orbs

    
    
