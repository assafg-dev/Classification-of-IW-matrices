#################################################################################################
#
#
#  A Sagemath Program for the classification of Integer Weighing matrices. The main function is 
#  ExhaustiveListIW(n,w,MinimizeRowLimit=4,max_entry=Infinity), which returns a list of all Integer Weighing 
#  matrices of order n and weight w, up to Hadamard equivalence. This list is exhaustive, but may contain repetitions 
#  of Hadamard equivalent matrices. Putting MinimizeRowLimit=n will give a fully classified list, but it will take a 
#  long time to compute. The default value is 4, which gives a  longer list, but still exhaustive in the sense that all 
#  matrices of order n and weight w are present, up to Hadamard equivalence.
#
# The algorithm is using the function Nsoks() which finds all ways to express n=\sum_i s_i^2 as a sum of r squares.
#
# Reference: AN ALGORITHM FOR CONSTRUCTING AND CLASSIFYING
# THE SPACE OF SMALL INTEGER WEIGHING MATRICES. "https://arxiv.org/pdf/2304.09495"
#
#################################################################################################

load("NSOKS.sage") 

def HadamardSpace(d): #Return a list of all Hadamard (+-1)-vectors of size d that begin with -1.
    SpaceSize = 2^(d-1)
    L=[ZZ(n).digits(2) for n in range(SpaceSize)]
    L1 = [x+[0]*(d-len(x)-1) for x in L]
    return([[-1]+[2*y-1 for y in x] for x in L1])

def IsBegWithPos(L): #Returns True if L[0]>0. Otherwise return False.
    for x in L:
        if x>0:
            return(True)
        if x<0:
            return(False)
    return(False)

def goodPerm(L,s):#Given two lists L,s of the same length, check that there is no -1 in s corresponding to 0 in L.
    for i in range(1,len(L)):
        if (L[i]==0) and (s[i]==-1) : return False
    return True

def normAboveAgainstMatrix(AboveMatrix,R2):#AboveMatrix is a given IW partial matrix. R2 is a new row that we want to add to the matrix. We normalize R2[i]<0 if the column above it in AboveMatrix is zero.
    for i in range(len(R2)):
        if AboveMatrix.column(i)==0:
            R2[i]=-abs(R2[i])
    return R2

def normAbove_old(myMAT):#MyMat is a given IW partial matrix. We normalize each column of MyMat to begin with a negative entry.
    for i in range(myMAT.ncols()):
        for j in range(myMAT.nrows()):
            if myMAT[j,i]!=0:
                myMAT[j,:]*=-sign(myMAT[j,i])
                break
    return myMAT

def normAbove(myMAT,signs=False):#MyMat is a given IW partial matrix. We normalize each column of MyMat to begin with a negative entry.
    MAT=copy(myMAT)
    sgn=myMAT.ncols()*[0]
    for i in range(myMAT.ncols()):
        for j in range(myMAT.nrows()):
            if MAT[j,i]!=0:
                sgn[i]=-sign(MAT[j,i])
                MAT[:,i]*=sgn[i]
                break
    if signs:
        return MAT,sgn
    return MAT

def dpAgainstMatrix(AboveMatrix,L2): #We compute the norm of the product of L2 (a candidate ro given in a list form) against the rows of AboveMatrix.
    return AboveMatrix*L2


def OrderMat(SPMat,base,perm=False):
    """
    This procedure reorders the columns of SPMat (a partial IW) by increasing lex order. We interpret each column as represention of a number in base 'base'. This number should be sufficiently large to accomodate all possible entries in the matrix. 
    If perm=True, it also returns the permutation that realizes this ordering.
    """
    baseVec = base  
    SPMat=normAbove(SPMat)
    SPMatP=sorted(SPMat.columns(),key=lambda vec:baseVec*vec)
    if perm:
        pi=perm_between(SPMat.columns(),SPMatP)
        return matrix(SPMatP).transpose(),pi
    return matrix(SPMatP).transpose()

def NormalizeByColumns(Mat,base,Mon=False): 
    """
    This procedure normalizes a matrix by colums. That is, it returns the minimal matrix which is column equivalent to Mat. If Mon=True, then it also returns the monomial matrix M such that Ordered Mat=Mat*M.transpose().
    """
    c=Mat.nrows()
    if Mon:
        MatN,s=normAbove(Mat,signs=True)
        MatN1,pi=OrderMat(MatN,base[-c:],perm=True)
        M=diagonal_matrix(s)*pi.matrix()
        return MatN1,M
    else:
        MatN=normAbove(Mat)
        MatN1=OrderMat(MatN,base[-c:])
        return MatN1

def AllMonMatUpTo(n): #This gives the full list of all monomial matrices up to order n.
    Mon={}
    for m in range(1,n+1):
        H=HadamardSpace(m)
        P=[pi.matrix() for pi in SymmetricGroup(m)]
        Lm=[-diagonal_matrix(h)*p for h in H for p in P]   
        Mon[m]=Lm
    return Mon

def FindMinInHadClass(A,Mon,base): #This returns the minimal matrix in the class of A, by the row lex ordering.
    m=A.nrows(); n=A.ncols()
    CodeMin=m*[10^10]  #(originally n*[10^10])
    for M in Mon[m]:
        MA=M*A
        MAnormC=NormalizeByColumns(MA,base)
        MAnormCode=list(MAnormC*base) #originally list(base* MAnormC)
        if MAnormCode<CodeMin:
            CodeMin=MAnormCode
            MinMat=MAnormC
    return MinMat


def AllVectorsWeight(n,w,max_entry=Infinity): #This returns a list of all vectors from sors, including permutation and signing, that start with a negative entry. This is the full list of rows from which the rows of the weighing are taken.
    Pos=Nsoks(w,n,maxsq=min(sqrt(w),max_entry))
    AboveMat=matrix(n*[0])
    AllVectors=[]
    count=0
    sw=floor(sqrt(w))
    for Typ in Pos:
        sqlist=sum([mul*[sq] for sq,mul in Typ],[])
        MTyp=OrthogonalSignedPermutationsWithFirstNonZeroPositiveAgainstMatrix(AboveMat,sqlist,(0,0),sw)
        for x in MTyp:
            for j in range(len(x)):
                if x[j]>0:
                    break
                elif x[j]<0:
                    AllVectors.append(vector(x))
                    count+=1
                    break
    AllVectors.sort()
    return tuple(AllVectors)
        
    
def OrthogonalToAboveMatrix(AboveMatrix,FullRowList,HighestIndex,IndexSubset,Mon,base,MinimizeRowLimit=4):
    """
    This function computes a list of vectors that can be appended to the matrix AboveMat, plus a list of indices (see explanation below). The rows should be: 
    a) Orthogonal to AboveMat.
    b) The augmented matrix must be minimal in the col lex ordering.

    Input: AboveMat=The matrix we want to enlarge. Assumed to be minimal.
           FullRowList=The full list of all possible row vectors.
           HighestIndex=The index of the last row of AboveMatrix.
           IndexSubset=A subset of indices that is attached to AboveMat. The orthogonal vectors indices must belong to this list.
           Mon=A list of monomial matrices required for minimization.
           base=The code invariant base.

    The function loops over all row vectors whose index is taken from IndexSubset, not less than HighestIndex+1. For each choice it is first checked that it is orthogonal to the last row of AboveMat. If yes, it is then checked that the augmnted matrix is minimal. The function returns the list of all such vectors, together with the list of all indices of all orthogonal vectors (not just the minimal ones). This list will serve as the new IndexSubset in the next application of this function.
    """
    RowIndexList=[]
    OrthIndexList=[]
    lowest_row=AboveMatrix[-1] if AboveMatrix.nrows()>0 else 0
    #len(IndexSubset))
    for ii in IndexSubset:
        if ii<=HighestIndex:
            continue
        Row=FullRowList[ii]
        if AboveMatrix.nrows()==0 or Row*lowest_row==0: #sum(Row[i]*AboveMatrix[-1][i] for i in range(len(Row)))==0:
            OrthIndexList.append(ii)
            if AboveMatrix.nrows()>=MinimizeRowLimit:
                RowIndexList.append(ii)
                continue
            NewMat=AboveMatrix.stack(matrix(Row))
            NewMatMin=FindMinInHadClass(NewMat,Mon,base)
            if NewMat==NewMatMin:
                RowIndexList.append(ii)
    return RowIndexList,OrthIndexList


def ExhaustiveListIW(n,w,MinimizeRowLimit=4,max_entry=Infinity): 
    """
    Return a list of all Integer Weighing matrices of order n and weight w, up to Hadamard equivalence. The list is exhaustive, but may contain repetitions of Hadamard equivalent matrices. 

    Optional entries:
        MinimizeRowLimit=4: The number of rows in the matrix above which the minimization with respect to the Row-lex ordering is done. The higher the number, the more time it takes to compute, but the list will be shorter.

    max_entry=Infinity: The maximum allowed entry in the matrix. For example if max_entry=1, this will be a list of classical weighing matrices.
    """

    WeightVectors=AllVectorsWeight(n,w,max_entry=max_entry)
    #print(f'Number of possible row vectors: {len(WeightVectors)}')
    Mon=AllMonMatUpTo(MinimizeRowLimit)
    base_size=1+2*floor(sqrt(w))
    base=vector([base_size^(n-1-i) for i in range(n)])
    MatList=IterateInitials([],[],[],WeightVectors,Mon,base,MinimizeRowLimit,n)
    return MatList


## This function is the main recursive function that builds the list of all Integer Weighing matrices of order n and weight w, up to Hadamard equivalence. It starts with an empty matrix and iteratively adds rows from the WeightVectors list, checking orthogonality and minimality at each step.

def IterateInitials(MatList,HighestIndexList,IndexSubsetList,WeightVectors,Mon,base,MinimizeRowLimit,n,m=0):
    LRows=len(WeightVectors)
    if m==0:
        AboveMatrix=matrix(0,n)
        HighestIndex=-1
        IndexSubset=list(range(len(WeightVectors)))
        Short,Long=OrthogonalToAboveMatrix(AboveMatrix,WeightVectors,HighestIndex,IndexSubset,Mon,base,MinimizeRowLimit)
        MatList=[matrix(WeightVectors[s]) for s in Short]
        HighestIndexList=Short
        IndexSubsetList=[[i for i in range(s,LRows)] for s in Short]
        m=1
    if m==n:
        return MatList
    else:
        NewMatList=[]
        NewHighestIndexList=[]
        NewIndexSubsetList=[]
        for ii in range(len(MatList)):
            AboveMatrix=MatList[ii]
            HighestIndex=HighestIndexList[ii]
            IndexSubset=IndexSubsetList[ii]
            #t1=cputime()
            Short,Long=OrthogonalToAboveMatrix(AboveMatrix,WeightVectors,HighestIndex,IndexSubset,Mon,base,MinimizeRowLimit)
            #t2=cputime()-t1
            #print(t2)
            for s in Short:
                row=WeightVectors[s]
                
                NewAboveMatrix=AboveMatrix.stack(matrix(row))
                NewMatList.append(NewAboveMatrix)
                high=s
                index_sub=[jj for jj in Long if jj>high]
                NewHighestIndexList.append(high)
                NewIndexSubsetList.append(index_sub)
        #print(f'{len(NewMatList)=}')
        MatList=IterateInitials(NewMatList,NewHighestIndexList,NewIndexSubsetList,WeightVectors,Mon,base,MinimizeRowLimit,n,m+1)
        return MatList


#### This is an old program for Nsoks. Not is use.
            
def sors(n,r,maxsq):  ### Find all ways to express n=\sum_i s_i^2 as a sum of r squares, with maxsq>=s_1>=s_2>=...>=s_r.
    #n0=RDF(n). This is NOT our best algorithm (TODO: look for the more recent 'nsoks').
    n0=n
    if r==1:
        s=sqrt(n0)
        fs=floor(s)
        if s==fs and s<=maxsq:
            return [[s]]
        else:
            return false
    else:
        sors2=[]
        for x in range(floor(sqrt(n0/r)),min(floor(sqrt(n0)),maxsq)+1):
            m=n-x^2
            #print x
            sors1=sors(m,r-1,x)
            if sors1:
                sors2+=[[x]+sors1[i] for i in range(len(sors1))   ]
           # print "sors2=",sors2
        if len(sors2)>0:
            return sors2
        else:
            return false
       
            



def OrthogonalSignedPermutationsWithFirstNonZeroPositiveAgainstMatrix(AboveMat,L,Lindex,MaxV):
    ### TODO: AboveMat is not relevant here, remove it from input.
    """
    This precedure produces a list of all vectors of type L (i.e. Hadamard equivalent to L) that are orthogonal to AboveMat.
    Input:
          AboveMat = a partial IW matrix.
          L = The given type of the orthogonal row.
          Lindex = The index of L in the list of 'sors'.
          maxV = An upper bound of all modulii of all matrix entries.

    Output: A list of pairs: ( [index in sors, index in permutations, index in signings], new orthogonal row)
    """
    P = Permutations(L).list()
    d = len(L)
    S = HadamardSpace(d)
    #ln=AboveMat.nrows()+1
    #SL=[diagonal_matrix(v)*p.matrix() for v in HadamardSpace(ln) for p in SymmetricGroup(ln)]
    #SL = HadamardSpace(AboveMat.nrows()+1)
    SP = []
    #s = []
    #sd = [] 
    sd1 = []
    #sd2 = []
    #codeBase = 1+2*MaxV
    #nR=AboveMat.nrows()
    #print(AboveMat)
    #cB=(vector([codeBase^(nR-j) for j in range(nR)]))*AboveMat
    for pi in range(Lindex[1],len(P)):
        p = P[pi]
        #s0=Lindex[2] if pi==Lindex[1] else 0
        s0=0
        for si in range(s0,len(S)):
            sn=S[si]
            if (goodPerm(p,sn)): #Take only the signing at nonzero entries of the vector. This saves a lot of time.
                r =vector([p[i]*sn[i] for i in range(d)])
                sd1.append(r)
                
                
               # if true:
                #if dpAgainstMatrix(AboveMat,r)==0: # Is the vector orthogonal?
                    #r=normAboveAgainstMatrix(AboveMat,r)
                    #NewMat=matrix(nR+1,d,AboveMat.list()+r)
                    #signedPermutaionsM = [diagonal_matrix(v)*p.matrix() for v in HadamardSpace(nR+1) for p in SymmetricGroup(nR+1)]
                    #for sPM in signedPermutaionsM:
                    #    OrederedSnewMat=orderMat(sPM*NewMat) #This is for the new algorithm (TODO: continue)
                """if not(r in SP):
                    SP.append(r)
                    R2i=r
                    M1 = cB+R2i #This computes the new code invariant of the (potential) augmented matrix.
                    M1s = sorted(M1)
                    if not(M1s in s):
                        M1m = cB-R2i #This is the same with -the row.
                        M1sm = sorted(M1m)
                        if not(M1sm in s): #Only consider row if it contributes new code invariant.
                            s.append(M1s)
                            sd.append([[Lindex[0],pi,si],R2i])  
                """ 
                                
    return(sd1) #Originally return(sd)

def LEcodeVector(cv1,cv2): #This asks if two vectors cv1<=cv2 under the lex order (entries are ordered by integer ordering).
    for i in range(len(cv1)):
        if cv1[i]<cv2[i]: return true
        if cv1[i]>cv2[i]: return false
    return true



