def eigenvector_similarity1(G1,G2):
   
    E1=matrix(RDF,G1).eigenvectors_right()
    E2=matrix(RDF,G2).eigenvectors_right()
    Inconclusive=True
    print("find perm")
    i0=0
    while(Inconclusive and i0<=G1.nrows()-1):
        print(i0)
        lam1=E1[i0][0]
        lams2=[Round(E2[j][0]) for j in range(len(E2))]
        ilam=lams2.index(Round(lam1))
        if lams2.count(Round(lam1))>1:  ###Eigenvalue not simple
           i0+=1
           continue
        print ("lam1 =",lam1)
        lam2=E2[ilam][0]
        v=E1[i0][1]
        w=E2[ilam][1]
        v=v[0]/sqrt(v[0]*v[0]); v=v*sign(max(v)+min(v))
        w=w[0]/sqrt(w[0]*w[0]); w=w*sign(max(w)+min(w))
        if len(Set(map(Round,list(w))))<len(w) or Set(map(Round,list(w)))!=Set(map(Round,list(v))):
           aa=1
        else:
           print ("Conclusive",i0)
           Inconclusive=False
        i0+=1
        print ("Inconclusive=",Inconclusive)
        print(Set(map(Round,list(w))),Set(map(Round,list(v))))
    sigr=perm_between(list(map(Round,list(w))),list(map(Round,list(v))))
    print ("sigr=",sigr)
    return sigr

def J(n):
    return matrix(n,n^2*[1])

def apply(F,G):
    n=G.nrows()
    lG=G.list()
    lG=list(map(F,lG))
    return matrix(n,lG)  

  
def order_by_multiplicity(E):
    n=len(E)
    ev=[round(100*E[i][0].real()) for i in range(n)]
    D={}
    for e in Set(ev):
        D[e]=[]
        for i in range(n):
            if e==ev[i]:
                D[e].append(E[i][1][0])
    return D


def eigenvector_similarity2(G1,G2):
    
    E1=matrix(RDF,G1).eigenvectors_right()
    E2=matrix(RDF,G2).eigenvectors_right()
    D1=order_by_multiplicity(E1)
    D2=order_by_multiplicity(E2)
    #print G1-G1.transpose()
   # print (G1).charpoly().factor()
    Inconclusive=True
    print ("find perm")
    i0=0
    Mv=matrix(G1.nrows(),0)
    Mw=matrix(G2.nrows(),0)
    while(Inconclusive and i0<=G1.nrows()-1):
      #  print i0
        lam1=E1[i0][0]
        lams2=[Round(E2[j][0]) for j in range(len(E2))]
        ilam=lams2.index(Round(lam1))
        if lams2.count(Round(lam1))>1:  ###Eigenvalue not simple
           i0+=1
           continue
       # print "lam1 =",lam1
        lam2=E2[ilam][0]
        v=E1[i0][1]
        w=E2[ilam][1]
        v=v[0]/sqrt(v[0]*v[0]); v=v*sign(max(v)+min(v))
        w=w[0]/sqrt(w[0]*w[0]); w=w*sign(max(w)+min(w))
        lv=list(map(Round,list(v)))
        lw=list(map(Round,list(w)))
      #  print lv,lw
        if len(Set(lw))==len(w) and len(Set(lv))==len(v):
         #  print "Conclusive",i0
           Inconclusive=False
           sigr=perm_between(lw,lv)
           print ("sig=",sigr)
           return sigr
        Mv=Mv.augment(matrix(G1.nrows(),1,lv))
        Mw=Mw.augment(matrix(G1.nrows(),1,lw))
        i0+=1
     #   print "Inconclusive=",Inconclusive
     #   print Set(map(Round,list(w))),Set(map(Round,list(v)))
    Lv=Mv.rows()
    Lv=list(map(str,Lv))
    Lw=Mw.rows()
    Lw=list(map(str,Lw))
    return Lw,Lv
   # print "Mv==Mw",Mv==Mw
    sigr=perm_between(Lw,Lv)
  #  print "here"
  #  print "sigr=",sigr
   # print "G1==G2",G1==G2
    return sigr

def orth_maximize(A,i):
    c=A.column(i)
    no=c.norm()
    a,b=c/no
    a=a.real(); b=b.real()
    O=matrix(RDF,2,[a,b,-b,a])
    return O*A

def eigenvector_similarity(G1,G2,AllPerms=False):
   # print G1.charpoly().factor()
    E1=matrix(RDF,G1).eigenvectors_right()
    E2=matrix(RDF,G2).eigenvectors_right()
    D1=order_by_multiplicity(E1)
    D2=order_by_multiplicity(E2)
    #print (G1).charpoly().factor()
    Inconclusive=True
    #print "find perm"
    i0=0
    Mv=matrix(G1.nrows(),0)
    Mw=matrix(G2.nrows(),0)
    
    for k in D1.keys():
        
        multiplicity=len(D1[k])
       
        #print "mult=",multiplicity
        if multiplicity==1:
            v=D1[k][0]
            w=D2[k][0]
            v=v*sign(max(v)+min(v))
            w=w*sign(max(w)+min(w))
            lv=list(map(Round,list(v)))
            lw=list(map(Round,list(w)))
           
            #print lw,lv
            if len(Set(lw))==len(w) and len(Set(lv))==len(v):
               print ("Conclusive",i0)
               
               sigr=perm_between(lw,lv)
               #print "sig=",sigr
               return sigr
            else:
                Mv=Mv.augment(matrix(G1.nrows(),1,lv))
                Mw=Mw.augment(matrix(G1.nrows(),1,lw))
               

        elif multiplicity>=3:
            continue
            A1=matrix(D1[k]); A2=matrix(D2[k])
            A1=A1.gram_schmidt()[0]
            A2=A2.gram_schmidt()[0]
            lv=[c*c for c in A1.columns()]
            lw=[c*c for c in A2.columns()]
            lv=list(map(Round,lv)); lw=list(map(Round,lw))
    
        elif multiplicity==2:  ### Multiplicity 2

            A1=matrix(D1[k]); A2=matrix(D2[k])

            A1=A1.gram_schmidt()[0]
            A2=A2.gram_schmidt()[0]
            
        #print A2[0].norm()
            j=0
           
            while A1.column(j).norm()<1e-7:
                  j+=1
            
            #print A1.column(j)
            A1=orth_maximize(A1,j)
            v1=A1.row(0); v2=A1.row(1)
            v1=v1*sign(max(v1)+min(v1))
            v2=v2*sign(max(v2)+min(v2))

            for i in range(A1.ncols()):            	
                A21=orth_maximize(A2,i)
                w1=A21.row(0); w2=A21.row(1)
                w1=w1*sign(max(w2).real()+min(w2).real())
                lv1=list(map(Round,list(v1)))
                lw1=list(map(Round,list(w1)))
                lv2=list(map(Round,list(v2)))
                lw2=list(map(Round,list(w2)))
                print ('after')
                V=matrix(2,len(v1),lv1+lv2)
                W=matrix(2,len(w1),lw1+lw2)
                Vc=V.columns()
                Wc=W.columns()
                Vc.sort()
                Wc.sort()
                #print "slv1=",slv1
               # print "slw1=",slw1
                if Vc==Wc:
                 #  print "here"
                   lv=lv2
                   lw=lw2
                   Mv=Mv.augment(matrix(G1.nrows(),1,lv1))
                   #Mv=Mv.augment(matrix(G1.nrows(),1,lv2))
                   Mw=Mw.augment(matrix(G1.nrows(),1,lw1))
                   #Mw=Mw.augment(matrix(G1.nrows(),1,lw2))
                   
                   break


    Lv=Mv.rows()
    Lv=list(map(str,Lv))
    Lw=Mw.rows()
    Lw=list(map(str,Lw))
    #print "Mv==Mw",Mv==Mw
    #print "Mv=%s"%Mv
    #print '\n'
    #print "Mw=%s"%Mw
    #print '\n'
    #print Lw,Lv
    #print "Lw=",Lw
    #print "Lv=",Lv
    if AllPerms:
       return Lw,Lv
       return all_perms(Lw,Lv)
    sigr=perm_between(Lw,Lv)
    #print "sigr=",sigr
    #print "here"
    if sigr:
       G11=copy(G1)
       G11.permute_rows_and_columns(sigr,sigr)
       #print G11==G2
    #print "G1==G2",G1==G2
    return sigr


              

def eigenvector_similarity3(G1,G2,AllPerms=False):
   # print G1.charpoly().factor()
    E1=matrix(RDF,G1).eigenvectors_right()
    E2=matrix(RDF,G2).eigenvectors_right()
    D1=order_by_multiplicity(E1)
    D2=order_by_multiplicity(E2)
    #print (G1).charpoly().factor()
    Inconclusive=True
    #print "find perm"
    i0=0
    Mv=matrix(G1.nrows(),0)
    Mw=matrix(G2.nrows(),0)
    count=0
    for k in D1.keys():
        multiplicity=len(D1[k])
        #print "mult=",multiplicity
        if multiplicity==1:
            count+=1
            v=D1[k][0]
            w=D2[k][0]
            if Round(max(v)+min(v))==0:
                continue

            v=v*sign(max(v)+min(v))
            w=w*sign(max(w)+min(w))
            lv=list(map(Round,list(v)))
            lw=list(map(Round,list(w)))
            #print lw,lv
            if len(Set(lw))==len(w) and len(Set(lv))==len(v):
               print ("Conclusive",i0)
               
               sigr=perm_between(lw,lv)
               #print "sig=",sigr
               return sigr
            else:
                Mv=Mv.augment(matrix(G1.nrows(),1,lv))
                Mw=Mw.augment(matrix(G1.nrows(),1,lw))
    

        
        elif multiplicity>=2:  ### Multiplicity 2
            
            A1=matrix(D1[k]); A2=matrix(D2[k])
            A1=A1.gram_schmidt()[0]
            A2=A2.gram_schmidt()[0]
            Nv=[Round(v.norm()) for v in A1.columns()]
            Nw=[Round(w.norm()) for w in A2.columns()]
            Nvs=copy(Nv)
            Nws=copy(Nw)
            Nvs.sort()
            Nws.sort()
            if Nvs==Nws:
               Mv=Mv.augment(matrix(G1.nrows(),1,Nv))
               Mw=Mw.augment(matrix(G1.nrows(),1,Nw))
       
       
        Mv.augment(matrix(G1.nrows(),1,[Round(RDF(G1[i,i])) for i in range(G1.nrows())] ))
        Mw.augment(matrix(G1.nrows(),1,[Round(RDF(G2[i,i])) for i in range(G1.nrows())] ))
	
        #Mv=Mv.augment(matrix(G1.nrows(),1,lv))
        #Mw=Mw.augment(matrix(G1.nrows(),1,lw))
       
      
    Lv=Mv.rows()
    Lv=list(map(str,Lv))
    Lw=Mw.rows()
    Lw=list(map(str,Lw))
    #print "Mv==Mw",Mv==Mw
    #print "Mv=%s"%Mv
    #print '\n'
    #print "Mw=%s"%Mw
    #print '\n'
    #print Lw,Lv
    #print "Lw=",Lw
    #print "Lv=",Lv
    if AllPerms:
       return Lw,Lv
       return all_perms(Lw,Lv)
    sigr=perm_between(Lw,Lv)
    #print "sigr=",sigr
    #print "here"
    if sigr:
       G11=copy(G1)
       G11.permute_rows_and_columns(sigr,sigr)
       #print G11==G2
    #print "G1==G2",G1==G2
    return sigr


##### Given two lists L1,L2, return a triple (pi,Groups,sigma) where pi,sigma are permutations and Groups is a list of symmetric groups [S1,S2,..,Sk] on  *disjoint* sub intervals of  [1,2,..,len(L1)]. All permutations 'per' bwtween L1 and L2 are of the form pi*g*sigma where g is in the product of the Si.  'per' satisfies that  L2[per(i+1)-1]=L1[i] for all i.

def all_perms(L1,L2):
    L1s=copy(L1)
    L2s=copy(L2)
    L1s.sort()
    L2s.sort()
    assert L1s==L2s
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
    return pi,Groups,sig

def prune(A,B,pi,Gs,sig,i):
    Aper=copy(A)
    Bper=copy(B)
    n=A.nrows()
    Aper.permute_rows(sig)
    Bper.permute_rows(pi^-1)
    S=SymmetricGroup(n)
    D=Gs[i].domain()
    D=[d-1 for d in D]
    BCols=Bper[D].columns()
    BCols.sort()
    Prunei=[]
    for q in Gs[i]:
        p=S(q)
        C=copy(Aper)
        C.permute_rows(p)
        CCols=C[D].columns()
        CCols.sort()
        
        #print CCols,BCols
        if BCols==CCols:
            Prunei.append(q)
    return Prunei


def initial_permutation_orbits(G,H):
    M1=G
    M2=H
    U1=apply(ff2,apply(ff1,M1)^-1)^-1
    U2=apply(ff2,apply(ff1,M2)^-1)^-1
    G1=U1*U1.transpose()
    G2=U2*U2.transpose()
    L1,L2=eigenvector_similarity3(G1,G2,AllPerms=True)
    pi,Gs,sig=all_perms(L1,L2)
    return pi,Gs,sig

def permutation_tree(A,B):
    m=A.nrows()
    Sm=SymmetricGroup(m)
    PermTree=[]
    for i in range(m):
        A1=copy(A)
        B1=copy(B)
        if i+1<m:
            B1.permute_rows(Sm((m,i+1)))
        A1=A1[:m-1]
        B1=B1[:m-1]
        G3=A1*A1.transpose()
        G4=B1*B1.transpose()
        L3,L4=eigenvector_similarity3(G3,G4,AllPerms=True)
        pi2,Gs2,sig2=all_perms(L3,L4)
        if i+1<m:
            pi2=Sm((m,i+1))*Sm(pi2)
        else:
            pi2=Sm(pi2)
        sig2=Sm(sig2)
        j=0
        empty=False
        Pr=[]
        for G in Gs2:
            if G.cardinality()<=120:
                pr=prune(A,B,pi2,Gs2,sig2,j)
               
                if pr==[]:
                    empty=True
                    break
                
            else:
                pr=Gs2[j] 
            j+=1
            Pr.append(pr)

        if empty:
            print(i)
        if not(empty):
            PermTree.append((pi2,Pr,sig2))
            
    return PermTree




##############    Search Tree Algortihms for finding permutations between objects  ########################

def PermTree(A,B,Oracle,Reduction,n,remaining_perm='Default'):
    if remaining_perm=='Default':
        remaining_perm=list(range(1,n+1))
    if Oracle(A)!=Oracle(B):
        return False
    if n==1:
        return remaining_perm
    A1=Reduction(A,1)
    O1=Oracle(A1)
    for i in range(1,n+1):
        Bi=Reduction(B,i)
        if O1==Oracle(Bi):
            rm=copy(remaining_perm)
            rm.remove(remaining_perm[i-1])
            Pi=PermTree(A1,Bi,Oracle,Reduction,n-1,remaining_perm=rm)
            if Pi:
                perm=[remaining_perm[i-1]]+Pi
                return perm
    return False

def DiagonalCount(A):
    n=A.nrows()
    D=[A[i,i] for i in range(n)]
    S=Set(D)
    M={}
    for s in S:
        M[s]=D.count(s)
    return M

def OffDiagonalCount(A):
    n=A.nrows()
    OD=[A[i,j] for i in range(n) for j in range(n) if j!=i]
    S=Set(OD)
    M={}
    for s in S:
        M[s]=OD.count(s)
    return M

def OffDiagonalCountS(A):
    B=A^2
    n=A.nrows()
    OD=[B[i,j] for i in range(n) for j in range(n) if j!=i]
    S=Set(OD)
    M={}
    for s in S:
        M[s]=OD.count(s)
    return M

def Round(M):
    L=M.list()
    n=M.nrows()
    LR=[round(27*z.real()+39*z.imag()) for z in L]
    return matrix(n,LR)

def CharOracle(A):
    return Round(A).charpoly()

PermOracle = lambda A : (DiagonalCount(A),OffDiagonalCountS(A))

PermCharOracle = lambda A: (DiagonalCount(A),OffDiagonalCountS(A),CharOracle(A))

def Reduce(A,i):
    n=A.nrows()
    l=list(range(n))
    l.remove(i-1)
    return A[l,l]

def FullReduce(M,i):
    A,prev,rem=M
    prev1=copy(prev)
    rem1=copy(rem)
    prev1.append(rem[i-1])
    rem1.remove(rem[i-1])
    return (A,prev1,rem1)

def FullPermOracle(M):
    A,prev,rem=M
    Aprev=A[prev,prev]
    Arem=A[rem,rem]
    return (Aprev,)+PermOracle(Arem)

def FindPerm(A,B):
    n=A.nrows()
    S=SymmetricGroup(n)
    C=B[:,:]
    pi=S.random_element()
    C.permute_rows_and_columns(pi,pi)
    FA=(A,[],list(range(n)))
    FB=(C,[],list(range(n)))
    PL=PermTree(FA,FB,FullPermOracle,FullReduce,n)
    if not(PL):
        return False
    th=S((PL))
    return th*pi

def FindPermUsingGraphIsomorphism(A,B):
    GA=DiGraph(A,weighted=True)
    GB=DiGraph(B,weighted=True)
    Isom=GA.is_isomorphic(GB,edge_labels=True, certificate=True)
    if Isom[0]:
        Sn=SymmetricGroup(A.nrows())
        return Sn([l+1 for k,l in Isom[1].items()])
    return False

def FindManyPerms(A,B,tol=10):
    th0=FindPerm(A,B)
    if not(th0):
        return []
    L=[]
    for j in range(tol):
        th=FindPermUsingGraphIsomorphism(A,B)
        L.append(th*th0^-1)
    S=th.parent()
    G=S.subgroup(L)
    #print("|G|=",G.cardinality())
    return [g*th0 for g in G]
