/*
Purpose: Exact threshold test for one-dimensional rank-metric codes.
Parameters: q=3, m=6, n=6, k=1, minimum rank distance d=4.
Mathematical criterion: rk(x-lambda*g) = dim(W) + quotient tuple rank.
Expected output: 31 scalar orbits, each reported with rho=4 or rho=5.
  WantWitness controls printing only; positive witnesses are always verified.
*/
/**********************************************************************
  check_cr_614_q3.m
  Exhaustive threshold test for [6,1,4]_{3^6/3} rank-metric codes.

  g=(u_1,u_2,u_3,u_4,0,0), dim_F3 U=4, m=n=6.
  This program distinguishes rho(C)=4 from rho(C)=5.

  EXACT REDUCTIONS
  1. Full tail: W=<x_5,x_6>. If dim(W)<2, extend W to dimension 2
     and replace the tail by a basis. Every rk(x-lambda*g) can only
     increase, so a distance-5 witness exists iff a full-tail one does.
  2. Scalar orbits of W: x -> alpha*x preserves distance from C since
     C is F-linear, and changes W to alpha*W. Thus one W per scalar
     orbit suffices for each fixed U.
  3. Scalar orbits of U: a basis change is a rank-isometric coordinate
     transformation; multiplication of U by alpha rescales a generator.
     Both U and W have 31 scalar orbits among 11011 subspaces each.
     No Frobenius reduction is used.

  QUOTIENT / BAD-COSET TEST
  Put Q=F/W, dim_F3 Q=4. A tuple y in Q^4 is good precisely when
    rk_F3(y-(pi(lambda*u_i))_i) >= 3 for every lambda in F.
  The shifts form a subspace H of Q^4 with dimension 6, since
  lambda*U cannot lie in W for nonzero lambda (4>2).
  Thus there are 3^(16-6)=59049 cosets of H. A missing coset in the
  image of the rank<=2 tuples yields a distance-5 witness.

  MEMORY-SAVING EXACT BAD-SET ENUMERATION
  There are 814401 rank<=2 tuples. Instead of storing them, use
    Bad = union_{L <= Q, dim L=2} L^4.
  Every tuple of rank<=2 is in this union and every tuple in the union
  has rank<=2. There are 130 such L. For each L, project the eight
  basis vectors of L^4 to Q^4/H, then enumerate their image subspace.
  It has dimension <=8 and at most 6561 elements. Mark those cosets
  in a boolean table of length 59049. Overlaps are harmless. Stop for
  this W only when all cosets are covered or all 130 L are processed.
  Encoded ternary vector addition uses two five-coordinate blocks;
  integer addition modulo 3^10 is NOT used as vector addition.

  Every positive witness is reconstructed in F^6 and independently
  checked by ordinary rank computations for all 729 scalars. A negative
  result requires exhaustion of all 31 W-orbit representatives.
  WantWitness controls printing only, never verification.

  Edit only batching/output settings. Indices refer to this script's
  deterministic RREF order and the printed field defining polynomial.
**********************************************************************/
/********************** PARAMETERS **********************/
q := 3;
m := 6;
n := 6;
d := 4;
TargetDistance := 5;
LowerRadius := 4;
TailDim := n-d;                    // fixed = 2

StartRep := 1;
EndRep := 0;                       // 0 = last representative
StopAfterFirstRho4 := false;
StopAfterFirstRho5 := false;
WantWitness := true;               // false hides x; still verifies it
ProgressEveryW := 1;              // 0 disables periodic W messages
RunInternalChecks := true;
AutoRun := true;                   // false = load functions only

/********************** FIELDS AND TERNARY CONVERSIONS **********************/
K := GF(q);
F<a> := GF(q^m);
V := VectorSpace(K,m);
print "Field defining polynomial:", DefiningPolynomial(F);
error if &or[ &+[ F!(Eltseq(z)[i])*a^(i-1) : i in [1..m] ] ne z : z in F ],
    "Polynomial-coordinate conversion failed.";


DigitsQ := function(z,k)
    if k eq 0 then
        return [ K | ];
    end if;
    return [ K!((z div q^j) mod q) : j in [0..k-1] ];
end function;

IndexQ0 := function(S)
    if #S eq 0 then
        return 0;
    end if;
    return &+[ (Integers()!S[i])*q^(i-1) : i in [1..#S] ];
end function;

VectorIndex0 := function(v)
    return IndexQ0(Eltseq(v));
end function;

Vec := function(x)
    return V!Eltseq(F!x);
end function;

EltFromVec := function(v)
    return &+[ F!v[i]*a^(i-1) : i in [1..m] ];
end function;

FieldElements := [ EltFromVec(V!DigitsQ(z,m)) : z in [0..q^m-1] ];

RankWeight := function(L)
    return Dimension(sub< V | [ Vec(z) : z in L ] >);
end function;

UFromFieldElements := function(L)
    return sub< V | [ Vec(z) : z in L ] >;
end function;

BasisElements := function(U)
    return [ EltFromVec(V!b) : b in Basis(U) ];
end function;

MakeGenerator := function(U)
    error if Dimension(U) ne d, "Wrong dimension for U.";
    B := BasisElements(U);
    return B cat [ F!0 : j in [1..n-d] ];
end function;

PrintGeneratorFromU := procedure(U)
    g := MakeGenerator(U);
    print [ g[i]/g[1] : i in [1..n] ];
end procedure;

MinimumDistanceOneDim := function(g)
    return RankWeight(g);
end function;

// Independent final check: ordinary Magma subspace ranks, all 729 scalars.
DistanceToCode := function(x,g)
    error if #x ne #g, "x and g have different lengths.";
    best := m+1;
    for lambda in FieldElements do
        wt := RankWeight([ x[i]-lambda*g[i] : i in [1..#g] ]);
        if wt lt best then
            best := wt;
        end if;
    end for;
    return best;
end function;

/********************** COMPLETE SUBSPACE ENUMERATION **********************/
GaussianBinomialQ := function(k,s)
    error if s lt 0 or s gt k, "Invalid Gaussian-binomial parameters.";
    if s eq 0 or s eq k then
        return 1;
    end if;
    num := 1;
    den := 1;
    for i in [0..s-1] do
        num *:= q^k-q^i;
        den *:= q^s-q^i;
    end for;
    return num div den;
end function;

// All s-dimensional subspaces of a full K-vector space X, exactly once,
// via unique reduced-row-echelon matrices.  The binary pivot mask is only
// a combinatorial device; all free entries are enumerated over F_3.
SubspacesOfDimension := function(X,s)
    k := Dimension(X);
    error if Degree(X) ne k or #BaseRing(X) ne q,
        "SubspacesOfDimension expects a full K-vector space.";
    error if s lt 0 or s gt k, "Invalid subspace dimension.";
    Subs := [* *];
    for pmask in [0..2^k-1] do
        piv := [ j : j in [1..k] | (pmask div 2^(j-1)) mod 2 eq 1 ];
        if #piv ne s then
            continue;
        end if;
        slots := [* *];
        for i in [1..s] do
            for j in [piv[i]+1..k] do
                if j notin piv then
                    Append(~slots,<i,j>);
                end if;
            end for;
        end for;
        for code in [0..q^(#slots)-1] do
            vals := DigitsQ(code,#slots);
            M := ZeroMatrix(BaseRing(X),s,k);
            for i in [1..s] do
                M[i,piv[i]] := 1;
            end for;
            for j in [1..#slots] do
                M[slots[j][1],slots[j][2]] := vals[j];
            end for;
            Append(~Subs,sub< X | [ X!M[i] : i in [1..s] ] >);
        end for;
    end for;
    error if #Subs ne GaussianBinomialQ(k,s), "Subspace count mismatch.";
    return Subs;
end function;

// Membership bit mask.  The exponent is an index in the 729-element
// ambient vector space; using powers of 2 here is only a collision-free key.
SubspaceKey := function(U)
    return &+[ 2^VectorIndex0(V!v) : v in U ];
end function;

MultiplySubspace := function(U,alpha)
    return sub< V | [ Vec(alpha*EltFromVec(V!b)) : b in Basis(U) ] >;
end function;

ScalarOrbitRepresentatives := function(SubList)
    Reps := [* *];
    Seen := { Integers() | };
    for U in SubList do
        key := SubspaceKey(U);
        if key notin Seen then
            Append(~Reps,U);
            for alpha in FieldElements do
                if alpha ne 0 then
                    Include(~Seen,SubspaceKey(MultiplySubspace(U,alpha)));
                end if;
            end for;
        end if;
    end for;
    error if #Seen ne #SubList, "Scalar orbit coverage check failed.";
    return Reps;
end function;

/********************** LOW-RANK TUPLE SUBSPACES **********************/
// Number of h-by-len matrices over F_q of rank exactly r.
RankMatrixCountQ := function(h,len,r)
    if r eq 0 then
        return 1;
    end if;
    num := 1;
    den := 1;
    for i in [0..r-1] do
        num *:= (q^h-q^i)*(q^len-q^i);
        den *:= q^r-q^i;
    end for;
    return num div den;
end function;

// All 130 two-spaces in the four-dimensional quotient coordinate space.
// Each entry is an 8-by-16 matrix whose rows form a basis of L^4.
BuildLowRankSpaces := function()
    X := VectorSpace(K,4);
    Planes := SubspacesOfDimension(X,2);
    error if #Planes ne 130, "Expected 130 quotient two-spaces.";
    LowRankSpaces := [* *];
    for L in Planes do
        B := Basis(L);
        A := ZeroMatrix(K,8,16);
        for i in [1..4] do
            for t in [1..2] do
                for j in [1..4] do
                    A[2*(i-1)+t,4*(i-1)+j] := B[t][j];
                end for;
            end for;
        end for;
        if RunInternalChecks then
            error if Rank(A) ne 8, "Wrong dimension for L^4.";
        end if;
        Append(~LowRankSpaces,A);
    end for;
    return LowRankSpaces;
end function;

// Add encoded five-dimensional F3 vectors without carries.
BuildBlockAdditionTable := function()
    block := q^5;
    digits := [ DigitsQ(z,5) : z in [0..block-1] ];
    return [ [ IndexQ0([ digits[x+1][j]+digits[y+1][j] : j in [1..5] ])
               : y in [0..block-1] ] : x in [0..block-1] ];
end function;

AddKey := function(x,y,Add)
    block := q^5;
    return Add[(x mod block)+1][(y mod block)+1]
         + block*Add[(x div block)+1][(y div block)+1];
end function;

// Enumerate the span of independent ten-coordinate rows, exactly once.
ImageSubspaceKeys := function(E,rank,Add)
    Keys := [ Integers() | 0 ];
    for i in [1..rank] do
        b := VectorIndex0(E[i]);
        twice := AddKey(b,b,Add);
        old := Keys;
        Keys := old cat [ AddKey(z,b,Add) : z in old ]
                    cat [ AddKey(z,twice,Add) : z in old ];
    end for;
    error if #Keys ne q^rank, "Image-subspace enumeration failed.";
    return Keys;
end function;

/********************** H-COSET REDUCTION **********************/
PivotColumns := function(E)
    piv := [ Integers() | ];
    for i in [1..Nrows(E)] do
        found := 0;
        for j in [1..Ncols(E)] do
            if E[i,j] ne 0 then
                found := j;
                break;
            end if;
        end for;
        if found ne 0 then
            Append(~piv,found);
        end if;
    end for;
    return piv;
end function;

// Reduce z modulo the row space of E by zeroing all pivot coordinates.
// The remaining free coordinates are the unique representative in the
// chosen coordinate complement; encode them as a base-3 integer.
CanonicalCosetKey := function(z,E,piv,Free)
    v := z;
    for i in [1..#piv] do
        p := piv[i];
        if v[p] ne 0 then
            c := v[p]/E[i,p];
            for j in [p..Ncols(E)] do
                v[j] -:= c*E[i,j];
            end for;
        end if;
    end for;
    if RunInternalChecks then
        error if &or[ v[p] ne 0 : p in piv ],
            "Coset reduction failed to zero a pivot coordinate.";
    end if;
    return IndexQ0([ v[j] : j in Free ]);
end function;

ComplementVectorFromKey := function(key,nbits,Free)
    vals := DigitsQ(key,#Free);
    v := [ K!0 : j in [1..nbits] ];
    for j in [1..#Free] do
        v[Free[j]] := vals[j];
    end for;
    return v;
end function;

/********************** ONE W AND WITNESS RECONSTRUCTION **********************/
// Results: hasWitness, x, independently computed distance.
FindGoodTupleForW := function(U,W,LowRankSpaces,Add)
    s := Dimension(W);
    error if s ne TailDim, "This q=3 search uses the exact full-tail reduction s=2.";
    h := m-s;
    error if h ne 4 or TargetDistance-s ne 3,
        "Unexpected quotient parameters for the optimized q=3 test.";

    Q,pi := quo< V | W >;
    error if Dimension(Q) ne h or Degree(Q) ne h,
        "The quotient must use h standard coordinates.";

    B := BasisElements(U);
    nbits := h*d;

    // Six basis shifts generate H.  Injection follows from dim(U)=4>dim(W)=2.
    ShiftRows := [* *];
    for lambda in BasisElements(V) do
        flat := &cat[ Eltseq(pi(Vec(lambda*u))) : u in B ];
        Append(~ShiftRows,flat);
    end for;
    M := Matrix(K,m,nbits,&cat[ r : r in ShiftRows ]);
    error if Rank(M) ne m,
        "Translation subspace H should have dimension 6.";
    E := EchelonForm(M);
    piv := PivotColumns(E);
    error if #piv ne m, "Wrong number of H pivots.";
    Free := [ j : j in [1..nbits] | j notin piv ];
    error if #Free ne nbits-m, "Wrong complement dimension.";

    error if #Free ne 10, "Expected a ten-dimensional coset space.";

    // P is the linear projection to the free-coordinate complement of H.
    // Applying it to eight basis rows replaces projection of all 3^8 rows.
    P := ZeroMatrix(K,nbits,#Free);
    for j in [1..nbits] do
        unit := [ K!0 : k in [1..nbits] ];
        unit[j] := 1;
        coords := DigitsQ(CanonicalCosetKey(unit,E,piv,Free),#Free);
        for k in [1..#Free] do
            P[j,k] := coords[k];
        end for;
    end for;
    if RunInternalChecks then
        error if Rank(P) ne #Free or M*P ne ZeroMatrix(K,m,#Free),
            "Projection must have kernel H and rank 10.";
    end if;

    CosetCount := q^(#Free);
    Covered := [ false : j in [1..CosetCount] ];
    CoveredCount := 0;
    error if #LowRankSpaces ne 130, "Incomplete low-rank-space list.";
    for A in LowRankSpaces do
        D := A*P;
        r := Rank(D);
        D := EchelonForm(D);
        Keys := ImageSubspaceKeys(D,r,Add);
        for key in Keys do
            if not Covered[key+1] then
                Covered[key+1] := true;
                CoveredCount +:= 1;
            end if;
        end for;
        if CoveredCount eq CosetCount then
            return false,[ F | ],-1;
        end if;
    end for;

    goodKey := -1;
    for key in [0..CosetCount-1] do
        if not Covered[key+1] then
            goodKey := key;
            break;
        end if;
    end for;
    error if goodKey lt 0, "Missing good coset was not found.";

    // Chosen representative y in Q^4: pivot coordinates zero, free
    // coordinates given by goodKey.
    yflat := ComplementVectorFromKey(goodKey,nbits,Free);

    // Build an explicit section Q -> F_{3^6} by scanning all field elements.
    Qsize := q^h;
    Lift := [ F!0 : j in [1..Qsize] ];
    Assigned := [ false : j in [1..Qsize] ];
    for z in FieldElements do
        coords := Eltseq(pi(Vec(z)));
        j := IndexQ0(coords)+1;
        if not Assigned[j] then
            Lift[j] := z;
            Assigned[j] := true;
        end if;
    end for;
    error if not (&and Assigned), "Quotient section is not surjective.";

    x := [ F | ];
    for i in [1..d] do
        coords := [ yflat[(i-1)*h+j] : j in [1..h] ];
        Append(~x,Lift[IndexQ0(coords)+1]);
    end for;
    x := x cat BasisElements(W);       // exactly two tail coordinates
    error if #x ne n, "Witness has the wrong length.";

    actual := DistanceToCode(x,MakeGenerator(U));
    error if actual lt TargetDistance,
        "Independent witness verification FAILED.";
    error if actual gt TargetDistance,
        "Witness contradicts the theoretical upper bound rho <= n-1.";
    return true,x,actual;
end function;

/********************** PRECOMPUTATION AND COMPLETE SEARCH **********************/
ValidateParameters := procedure()
    error if q ne 3 or m ne 6,
        "This script is specialized to F_{3^6}/F_3.";
    error if n ne 6 or d ne 4 or TargetDistance ne 5 or LowerRadius ne 4,
        "Do not change the fixed code parameters of this file.";
    error if TailDim ne 2, "The full-tail proof used here requires n-d=2.";
    // Sphere-covering bound: radius 3 cannot cover F^{6} with |C|=q^m.
    BallRadius3 := &+[ RankMatrixCountQ(m,n,r) : r in [0..3] ];
    error if q^m*BallRadius3 ge q^(m*n),
        "The sphere-covering check does not certify rho >= 4.";
    error if TargetDistance ne n-1, "Unexpected upper bound.";
    error if StartRep lt 1 or EndRep lt 0, "Invalid batch parameters.";
    error if ProgressEveryW lt 0, "Progress interval must be nonnegative.";
    if RunInternalChecks then
        error if #FieldElements ne q^m or #Seqset(FieldElements) ne q^m,
            "Field enumeration failed.";
        for j in [1..q^m] do
            error if EltFromVec(Vec(FieldElements[j])) ne FieldElements[j]
                or VectorIndex0(Vec(FieldElements[j])) ne j-1,
                "Field/vector conversion failed.";
        end for;
    end if;
end procedure;

// Returns <scalar-orbit reps of W, low-rank spaces, ternary addition table>.  ScalarOrbitRepresentatives
// has already certified coverage of the complete 2-subspace list.
PrepareSearchData := function()
    ValidateParameters();

    t0 := Cputime();
    AllW := SubspacesOfDimension(V,TailDim);
    printf "All W with dim %o: %o; enumeration CPU %o s\n",
        TailDim,#AllW,Cputime(t0);
    error if #AllW ne 11011, "Unexpected number of 2-subspaces of F_3^6.";

    t0 := Cputime();
    WReps := ScalarOrbitRepresentatives(AllW);
    printf "%o scalar-orbit representatives for W; CPU %o s\n",
        #WReps,Cputime(t0);
    // 91 F_9-lines form one special orbit; the remaining 10920 spaces
    // form 30 generic orbits of size 364, hence 31 orbits in total.
    error if #WReps ne 31, "Unexpected number of scalar orbits on 2-spaces.";

    t0 := Cputime();
    LowRankSpaces := BuildLowRankSpaces();
    Add := BuildBlockAdditionTable();
    BadCount := &+[ RankMatrixCountQ(4,4,r) : r in [0..2] ];
    error if BadCount ne 814401, "Unexpected rank<=2 tuple count.";
    printf "Bad tuples: %o, represented by %o subspaces L^4; CPU %o s\n",
        BadCount,#LowRankSpaces,Cputime(t0);
    print "Cosets per W: 59049; maximum image-subspace size: 6561.";
    if RunInternalChecks then
        // Independent coordinate checks for both blocks of encoded addition.
        for j in [0..255] do
            x := (j*104729) mod q^10;
            y := (j*7919+1) mod q^10;
            xx := DigitsQ(x,10);
            yy := DigitsQ(y,10);
            expected := IndexQ0([ xx[k]+yy[k] : k in [1..10] ]);
            error if AddKey(x,y,Add) ne expected, "Ternary addition failed.";
        end for;
    end if;
    return <WReps,LowRankSpaces,Add>;
end function;

FindDistanceAtLeastT_Hybrid := function(U,Data)
    WReps := Data[1];
    LowRankSpaces := Data[2];
    Add := Data[3];
    error if #WReps ne 31,
        "Incomplete W-orbit list: refusing to certify a negative result.";

    t0 := Cputime();
    printf "Checking all %o scalar-orbit representatives of 2-spaces W...\n",#WReps;
    for j in [1..#WReps] do
        has,x,actual := FindGoodTupleForW(U,WReps[j],LowRankSpaces,Add);
        if has then
            printf "  Found at W-orbit representative %o/%o; CPU %o s\n",
                j,#WReps,Cputime(t0);
            return true,x,WReps[j],actual,j;
        end if;
        if ProgressEveryW gt 0 and j mod ProgressEveryW eq 0 then
            printf "  Checked W-orbit representatives %o/%o; CPU %o s\n",
                j,#WReps,Cputime(t0);
        end if;
    end for;
    printf "  Finished all %o W-orbit representatives; CPU %o s\n",
        #WReps,Cputime(t0);
    return false,[ F | ],sub< V | [] >,-1,#WReps;
end function;

ReportResult := procedure(has,x,W,actual,tested)
    if has then
        printf "Result: rho(C) = %o.\n",TargetDistance;
        printf "Independent DistanceToCode(x,g) = %o (all %o scalars).\n",
            actual,q^m;
        print "Basis of W:",BasisElements(W);
        if WantWitness then
            print "Witness x:",x;
        end if;
    else
        printf "Exhausted all %o scalar-orbit representatives of 2-spaces W.\n",tested;
        print "By the exact full-tail and W-scalar-orbit reductions, no distance-5 witness exists.";
        printf "Certified: rho(C) <= %o.\n",TargetDistance-1;
        printf "Using the verified sphere-covering lower bound: rho(C) = %o.\n",LowerRadius;
    end if;
end procedure;

TestCustomU := procedure(L)
    ValidateParameters();
    U := UFromFieldElements([ F!z : z in L ]);
    error if Dimension(U) ne d,
        "The supplied elements have the wrong span dimension.";
    g := MakeGenerator(U);
    print "Custom U; normalized generator for an equivalent code (basis may change):";
    PrintGeneratorFromU(U);
    print "Minimum distance:",MinimumDistanceOneDim(g);
    print "Defining polynomial:",DefiningPolynomial(F);
    Data := PrepareSearchData();
    t0 := Cputime();
    has,x,W,actual,tested := FindDistanceAtLeastT_Hybrid(U,Data);
    printf "Search CPU: %o s\n",Cputime(t0);
    ReportResult(has,x,W,actual,tested);
end procedure;

RunSearch := procedure()
    ValidateParameters();
    totalTime := Cputime();
    print "Exhaustive hybrid search for [6,1,4]_{3^6/3}";
    print "Defining polynomial:",DefiningPolynomial(F);
    print "Exact reductions: full tail dim(W)=2; scalar orbits on U and W; H-coset bad-set test.";

    Data := PrepareSearchData();

    t0 := Cputime();
    AllU := SubspacesOfDimension(V,d);
    error if #AllU ne 11011, "Unexpected number of 4-subspaces of F_3^6.";
    Reps := ScalarOrbitRepresentatives(AllU);
    printf "%o U subspaces; %o scalar-orbit representatives; CPU %o s\n",
        #AllU,#Reps,Cputime(t0);
    // 91 F_9-linear four-spaces form one special orbit; the remaining
    // 10920 spaces form 30 generic orbits of size 364, hence 31 in total.
    error if #Reps ne 31, "Unexpected number of scalar orbits on 4-spaces.";

    Last := #Reps;
    if EndRep ne 0 then
        Last := Min(EndRep,Last);
    end if;
    error if StartRep gt Last, "The requested batch is empty or out of range.";
    printf "Batch: representatives %o through %o of %o.\n",StartRep,Last,#Reps;

    Results := [* *];
    for idx in [StartRep..Last] do
        U := Reps[idx];
        g := MakeGenerator(U);
        print "----------------------------------------";
        printf "Representative %o/%o\n",idx,#Reps;
        PrintGeneratorFromU(U);
        error if #g ne n or MinimumDistanceOneDim(g) ne d,
            "Generator validation failed.";

        t0 := Cputime();
        has,x,W,actual,tested := FindDistanceAtLeastT_Hybrid(U,Data);
        printf "Search CPU: %o s\n",Cputime(t0);
        ReportResult(has,x,W,actual,tested);

        rho := LowerRadius;
        if has then
            rho := TargetDistance;
        end if;
        Append(~Results,<idx,rho>);

        if (rho eq 4 and StopAfterFirstRho4)
            or (rho eq 5 and StopAfterFirstRho5) then
            printf "Stopping after the first rho=%o example, as requested.\n",rho;
            break;
        end if;
    end for;

    print "========================================";
    print "Completed representatives <index,rho>:",Results;
    printf "rho=%o: %o; rho=%o: %o.\n",LowerRadius,
        #[ R : R in Results | R[2] eq LowerRadius ],TargetDistance,
        #[ R : R in Results | R[2] eq TargetDistance ];

    if #Results eq #Reps and StartRep eq 1 and Last eq #Reps then
        print "ALL scalar-orbit representatives classified.";
    else
        print "Only the listed representatives were classified (batch/early stop).";
        print "No conclusion is made for unprocessed U representatives.";
    end if;
    printf "Total CPU: %o s\n",Cputime(totalTime);
end procedure;

/********************** HOW TO RUN **********************/
// In a fresh Magma session:
//   load "check_cr_614_q3.m";
// The default AutoRun=true starts the complete search.
// For a batch, edit StartRep/EndRep at the top BEFORE loading.
//
// To test only one custom 4-space U, set AutoRun:=false, load, and enter e.g.
//   TestCustomU([ F!1, a, a^2, a^3 ]);
//
// The displayed generator uses an RREF basis of U and is normalized by
// its first entry.  Powers of a refer to THIS field's defining polynomial.
// Different source-field models must be matched by a field isomorphism.

if AutoRun then
    RunSearch();
end if;
