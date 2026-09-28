/*
Purpose: Exact threshold test for one-dimensional rank-metric codes.
Parameters: q=3, m=6, n=5, k=1, minimum rank distance d=3.
Mathematical criterion: rk(x-lambda*g) = dim(W) + quotient tuple rank.
Expected output: 94 scalar orbits, all expected to have rho=4.
WantWitness controls printing only; positive witnesses are always verified.
*/
/**********************************************************************
  check_cr_513_q3.m
  Exhaustive threshold test for [5,1,3]_{3^6/3} rank-metric codes.

  g = (u_1,u_2,u_3,0,0), dim_F3 <u_1,u_2,u_3> = 3.
  This program decides whether rho(C)=3 or rho(C)=4 by testing for a
  word at distance >=4.

  EXACT REDUCTION 1: IT IS ENOUGH TO TAKE dim(W)=2
  For x=(x_1,...,x_5), let W=<x_4,x_5>_F3. If dim(W)<2,
  extend W to a 2-space W' and replace the last two coordinates by a
  basis of W'. For every lambda, the span of the coordinates of
  x-lambda*g can only increase. Thus a distance-4 witness exists iff
  one exists with dim(W)=2; smaller tail dimensions need not be tested.

  EXACT REDUCTION 2: SCALAR ORBITS OF W
  If x is a witness with tail span W, alpha*x has tail span alpha*W.
  Since C is F_{3^6}-linear,
    min_lambda rk(alpha*x-lambda*g)
      = min_mu rk(alpha*(x-mu*g)) = min_mu rk(x-mu*g).
  Hence one scalar-orbit representative of W suffices for each fixed U.
  The orbit routine verifies coverage of all 11011 two-spaces.

  QUOTIENT / BAD-COSET TEST
  Fix dim(W)=2 and Q=F_{3^6}/W, of F3-dimension h=4. For each lambda,
    rk(x-lambda*g) = 2 + dim_F3 <pi(x_i)-pi(lambda*u_i):1<=i<=3>.
  Thus a quotient tuple y in Q^3 is good iff all its translates by
    H={ (pi(lambda*u_1),pi(lambda*u_2),pi(lambda*u_3)) : lambda in F }
  have rank at least 2. Since dim(U)=3>dim(W)=2, H has dimension 6.
  Let Bad be the tuples of rank 0 or 1. A good tuple exists iff the
  image of Bad in Q^3/H omits a coset. There are 3^(4*3-6)=729 cosets
  and 1+(3^4-1)*(3^3-1)/(3-1)=1041 bad tuples.

  SAFE SCALAR REDUCTION ON U
  Changing the F3-basis of U is a GL(3,3) coordinate rank isometry,
  extended by the identity on the last two coordinates. Replacing U
  by alpha*U rescales the generator. Thus one U per scalar orbit
  suffices: 94 representatives among 33880 three-spaces.
  There are 31 scalar orbits of two-spaces W. No Frobenius reduction.

  Every positive result is reconstructed in F_{3^6}^5 and independently
  verified by DistanceToCode using ordinary ranks for all 729 scalars.
  WantWitness controls printing only; verification always takes place.
  A negative result is reported only after every W representative is tested.

  Edit only batching/output parameters below. Representative indices
  belong to this script's deterministic RREF order and field model.
**********************************************************************/
/********************** PARAMETERS **********************/
q := 3;
m := 6;
n := 5;
d := 3;
TargetDistance := 4;
LowerRadius := 3;
TailDim := n-d;                    // fixed = 2

StartRep := 1;
EndRep := 0;                       // 0 = last representative
StopAfterFirstRho3 := false;
StopAfterFirstRho4 := false;
WantWitness := true;               // false hides x; still verifies it
ProgressEveryW := 10;              // 0 disables periodic W messages
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

/********************** THE 1041 BAD QUOTIENT TUPLES **********************/
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

// Here h=4, len=3, NeedDim=2.  Rank<2 means rank 0 or 1.
// We build it directly: zero plus, for every projective point <v> in F_3^4,
// all nonzero coefficient 3-tuples (c_1,c_2,c_3), giving rows c_i v.
BuildBadRankLessThan2 := function(h,len)
    error if h ne 4 or len ne 3,
        "This optimized bad-set constructor is specialized to h=4,len=3.";
    X := VectorSpace(K,h);
    Lines := SubspacesOfDimension(X,1);
    Bad := [* [ K!0 : j in [1..h*len] ] *];
    for L in Lines do
        v := Basis(L)[1];
        for code in [1..q^len-1] do
            coeff := DigitsQ(code,len);
            flat := &cat[ Eltseq(coeff[i]*v) : i in [1..len] ];
            Append(~Bad,flat);
        end for;
    end for;
    expected := RankMatrixCountQ(h,len,0)+RankMatrixCountQ(h,len,1);
    error if #Bad ne expected, "Bad-tuple count mismatch.";
    if RunInternalChecks then
        for flat in Bad do
            error if Rank(Matrix(K,len,h,flat)) ge 2,
                "Bad-set construction produced rank >=2.";
        end for;
    end if;
    return Bad;
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
FindGoodTupleForW := function(U,W,BadFlat)
    s := Dimension(W);
    error if s ne TailDim, "This q=3 search uses the exact full-tail reduction s=2.";
    h := m-s;
    error if h ne 4 or TargetDistance-s ne 2,
        "Unexpected quotient parameters for the optimized q=3 test.";

    Q,pi := quo< V | W >;
    error if Dimension(Q) ne h or Degree(Q) ne h,
        "The quotient must use h standard coordinates.";

    B := BasisElements(U);
    nbits := h*d;

    // Six basis shifts generate H.  Injection follows from dim(U)=3>dim(W)=2.
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

    // Bad+H covers precisely the H-cosets containing at least one bad tuple.
    Covered := { Integers() | };
    for z in BadFlat do
        Include(~Covered,CanonicalCosetKey(z,E,piv,Free));
    end for;

    CosetCount := q^(#Free);
    error if #Covered gt CosetCount, "Impossible coset count.";
    if #Covered eq CosetCount then
        return false,[ F | ],-1;
    end if;

    goodKey := -1;
    for key in [0..CosetCount-1] do
        if key notin Covered then
            goodKey := key;
            break;
        end if;
    end for;
    error if goodKey lt 0, "Missing good coset was not found.";

    // Chosen representative y in Q^3: pivot coordinates zero, free
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
    error if n ne 5 or d ne 3 or TargetDistance ne 4 or LowerRadius ne 3,
        "Do not change the fixed code parameters of this file.";
    error if TailDim ne 2, "The full-tail proof used here requires n-d=2.";
    // Sphere-covering bound: radius 2 cannot cover F^{5} with |C|=q^m.
    BallRadius2 := &+[ RankMatrixCountQ(m,n,r) : r in [0..2] ];
    error if q^m*BallRadius2 ge q^(m*n),
        "The sphere-covering check does not certify rho >= 3.";
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

// Returns <scalar-orbit reps of W, BadFlat>.  ScalarOrbitRepresentatives
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
    BadFlat := BuildBadRankLessThan2(m-TailDim,d);
    printf "Bad quotient tuples (rank < 2): %o; CPU %o s\n",
        #BadFlat,Cputime(t0);
    error if #BadFlat ne 1041, "Expected exactly 1041 bad tuples.";

    return <WReps,BadFlat>;
end function;

FindDistanceAtLeastT_Hybrid := function(U,Data)
    WReps := Data[1];
    BadFlat := Data[2];
    error if #WReps ne 31,
        "Incomplete W-orbit list: refusing to certify a negative result.";

    t0 := Cputime();
    printf "Checking all %o scalar-orbit representatives of 2-spaces W...\n",#WReps;
    for j in [1..#WReps] do
        has,x,actual := FindGoodTupleForW(U,WReps[j],BadFlat);
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
        print "By the exact full-tail and W-scalar-orbit reductions, no distance-4 witness exists.";
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
    print "Exhaustive hybrid search for [5,1,3]_{3^6/3}";
    print "Defining polynomial:",DefiningPolynomial(F);
    print "Exact reductions: full tail dim(W)=2; scalar orbits on U and W; H-coset bad-set test.";

    Data := PrepareSearchData();

    t0 := Cputime();
    AllU := SubspacesOfDimension(V,d);
    error if #AllU ne 33880, "Unexpected number of 3-subspaces of F_3^6.";
    Reps := ScalarOrbitRepresentatives(AllU);
    printf "%o U subspaces; %o scalar-orbit representatives; CPU %o s\n",
        #AllU,#Reps,Cputime(t0);
    // 28 F_27-lines form one special orbit; the remaining 33852 spaces
    // form 93 generic orbits of size 364, hence 94 orbits in total.
    error if #Reps ne 94, "Unexpected number of scalar orbits on 3-spaces.";

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

        if (rho eq 3 and StopAfterFirstRho3)
            or (rho eq 4 and StopAfterFirstRho4) then
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
//   load "check_cr_513_q3.m";
// The default AutoRun=true starts the complete search.
// For a batch, edit StartRep/EndRep at the top BEFORE loading.
//
// To test only one custom 3-space U, set AutoRun:=false, load, and enter e.g.
//   TestCustomU([ F!1, a, a^2 ]);
//
// The displayed generator uses an RREF basis of U and is normalized by
// its first entry.  Powers of a refer to THIS field's defining polynomial.
// Different source-field models must be matched by a field isomorphism.

if AutoRun then
    RunSearch();
end if;
