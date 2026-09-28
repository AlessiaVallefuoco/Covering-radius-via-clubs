/*
Purpose: Exact threshold test for one-dimensional rank-metric codes.
Parameters: q=3, m=6, n=6, k=1, minimum rank distance d=3.
Mathematical criterion: rk(x-lambda*g) = dim(W) + quotient tuple rank.
Expected output: 94 scalar orbits, classified individually; see README for evidence status.
  WantWitness controls printing only; positive witnesses are always verified.
*/
/**********************************************************************
  check_cr_613_q3.m
  Exact covering-radius test for [6,1,3]_{3^6/3} codes.
  Standalone Magma script; no external packages or input files.

  FIELD MODEL: F=F_3(a), a^6+a+2=0. Powers in the examples refer to
  this polynomial, not to the generator of a different GF(3^6) model.

  g=(u_1,u_2,u_3,0,0,0), dim_F3 U=3.
  The only possible covering radii are 4 and 5.

  EXACT REDUCTIONS
  Full tail: if W=<x_4,x_5,x_6> has dimension <3, extend it to W' of
  dimension 3 and replace the tail by a basis of W'. For every lambda,
  the coordinate span of x-lambda*g can only increase. Thus searching
  only dim(W)=3 is sufficient and loses no distance-5 witnesses.
  Scalar orbits of W: alpha*x has tail alpha*W and the same distance
  from C, since C is F-linear. For each fixed U it suffices to test
  one representative of each scalar orbit of three-spaces W.
  Scalar orbits of U: changing its F3-basis is a rank isometry on the
  first three coordinates; scaling U rescales the generator.
  There are 33880 three-spaces and 94 scalar orbits. No Frobenius
  reduction is used. Orbit coverage is checked during precomputation.

  SMALL BAD-COSET TEST
  For Q=F/W, dim Q=3, and y=(pi(x_1),pi(x_2),pi(x_3)),
    rk(x-lambda*g) = 3 + rk(y-(pi(lambda*u_i))_i).
  Let H be the image of lambda -> (pi(lambda*u_i))_i in Q^3.
  A distance-5 witness exists iff some H-coset contains no rank<=1
  tuple. There are exactly 1+(27-1)^2/2=339 bad tuples.

  IMPORTANT: dim(H) is computed, NOT assumed equal to 6.
  Its kernel is {lambda : lambda*U is contained in W}. For equal
  dimensions, a nonzero kernel exists exactly when W=alpha*U. Then
  the kernel is alpha times the scalar stabilizer field of U, which
  is F_3 or F_27. Thus dim(H)=6,5,3 and Q^3/H has 27,81,729 elements.
  Project the 339 bad tuples using a 9-by-(9-dim(H)) matrix and mark
  their cosets. A missing coset produces a witness; full coverage
  proves that this W has no witness. No random search is used.

  Positive witnesses are checked independently with all 729 scalars.
  Negative results require all 94 W representatives. The U and W
  representative lists coincide and are computed only once.

  QUICK EXAMPLES (also checked by the independent validation in this bundle):
    g4=(1,a,a^2,0,0,0)                 has rho=4;
    g5=(1,a,a^2+a^4,0,0,0)             has rho=5;
    x5=(0,a^5,a^3+a^4,1,a,a^2+a^4)    has distance 5 from <g5>.
  RunExamples() checks the explicit x5 directly and classifies both
  generators by the complete algorithm. It does not assume the results.

**********************************************************************/
/********************** PARAMETERS **********************/
q := 3;
m := 6;
n := 6;
d := 3;
TargetDistance := 5;
LowerRadius := 4;
TailDim := n-d;                    // fixed = 3

StartRep := 1;
EndRep := 0;                       // 0 = last representative
StopAfterFirstRho4 := false;
StopAfterFirstRho5 := false;
WantWitness := true;               // false hides x; still verifies it
ProgressEveryW := 10;              // 0 disables periodic W messages
RunInternalChecks := true;
AutoRun := true;                   // false = load functions only
ExamplesOnly := false;             // true = run just the three known examples

/********************** FIELDS AND TERNARY CONVERSIONS **********************/
K := GF(q);
R<t> := PolynomialRing(K);
FieldPolynomial := t^6+t+2;
error if not IsIrreducible(FieldPolynomial), "Field polynomial is reducible.";
F<a> := ext< K | FieldPolynomial >;
error if Order(a) ne q^m-1, "The fixed field generator is not primitive.";
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

// One representative of F^*/F3^*, selected in polynomial coordinates.
ScalarMultipliers := [ F | ];
for alpha in FieldElements do
    if alpha eq 0 then
        continue;
    end if;
    coords := Eltseq(Vec(alpha));
    first := Min([ i : i in [1..m] | coords[i] ne 0 ]);
    if coords[first] eq 1 then
        Append(~ScalarMultipliers,alpha);
    end if;
end for;
error if #ScalarMultipliers ne 364, "Wrong scalar-transversal size.";

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
            for alpha in ScalarMultipliers do
                if alpha ne 0 then
                    Include(~Seen,SubspaceKey(MultiplySubspace(U,alpha)));
                end if;
            end for;
        end if;
    end for;
    error if #Seen ne #SubList, "Scalar orbit coverage check failed.";
    return Reps;
end function;

/********************** THE 339 BAD QUOTIENT TUPLES **********************/
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

// Here h=3, len=3, NeedDim=2.  Rank<2 means rank 0 or 1.
// We build it directly: zero plus, for every projective point <v> in F_3^3,
// all nonzero coefficient 3-tuples (c_1,c_2,c_3), giving rows c_i v.
BuildBadRankLessThan2 := function(h,len)
    error if h ne 3 or len ne 3,
        "This optimized bad-set constructor is specialized to h=3,len=3.";
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
FindGoodTupleForW := function(U,W,BadMatrix)
    s := Dimension(W);
    error if s ne TailDim, "This q=3 search uses the exact full-tail reduction s=3.";
    h := m-s;
    error if h ne 3 or TargetDistance-s ne 2,
        "Unexpected quotient parameters for the optimized q=3 test.";

    Q,pi := quo< V | W >;
    error if Dimension(Q) ne h or Degree(Q) ne h,
        "The quotient must use h standard coordinates.";

    B := BasisElements(U);
    nbits := h*d;

    // Six basis shifts generate H; the map may have a nonzero kernel.
    ShiftRows := [* *];
    for lambda in BasisElements(V) do
        flat := &cat[ Eltseq(pi(Vec(lambda*u))) : u in B ];
        Append(~ShiftRows,flat);
    end for;
    M := Matrix(K,m,nbits,&cat[ r : r in ShiftRows ]);
    rH := Rank(M);
    error if rH notin [3,5,6], "Unexpected translation-space dimension.";
    E := EchelonForm(M);
    piv := PivotColumns(E);
    error if #piv ne rH, "Wrong number of H pivots.";
    Free := [ j : j in [1..nbits] | j notin piv ];
    error if #Free ne nbits-rH, "Wrong complement dimension.";

    // Projection onto the coordinate complement of H. A row z has key
    // IndexQ0(z*P); its kernel is exactly H, including the noninjective cases.
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
            "Projection does not have kernel H.";
    end if;
    error if Nrows(BadMatrix) ne 339 or Ncols(BadMatrix) ne 9,
        "Wrong bad-tuple matrix.";
    Images := BadMatrix*P;
    Covered := { IndexQ0(Eltseq(Images[i])) : i in [1..Nrows(Images)] };
    CosetCount := q^(#Free);
    error if CosetCount notin [27,81,729], "Unexpected coset count.";
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
    x := x cat BasisElements(W);       // exactly three tail coordinates
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
    error if n ne 6 or d ne 3 or TargetDistance ne 5 or LowerRadius ne 4,
        "Do not change the fixed code parameters of this file.";
    error if TailDim ne 3, "The full-tail proof used here requires n-d=3.";
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

// Returns <scalar-orbit reps of W, 339-by-9 bad-tuple matrix>.  ScalarOrbitRepresentatives
// has already certified coverage of the complete 3-subspace list.
PrepareSearchData := function()
    ValidateParameters();

    t0 := Cputime();
    AllW := SubspacesOfDimension(V,TailDim);
    printf "All W with dim %o: %o; enumeration CPU %o s\n",
        TailDim,#AllW,Cputime(t0);
    error if #AllW ne 33880, "Unexpected number of 3-subspaces of F_3^6.";

    t0 := Cputime();
    WReps := ScalarOrbitRepresentatives(AllW);
    printf "%o scalar-orbit representatives for W; CPU %o s\n",
        #WReps,Cputime(t0);
    // 28 F_27-lines form one special orbit; the remaining 33852 spaces
    // form 93 generic orbits of size 364, hence 94 orbits in total.
    error if #WReps ne 94, "Unexpected number of scalar orbits on 3-spaces.";

    t0 := Cputime();
    BadFlat := BuildBadRankLessThan2(m-TailDim,d);
    printf "Bad quotient tuples (rank < 2): %o; CPU %o s\n",
        #BadFlat,Cputime(t0);
    error if #BadFlat ne 339, "Expected exactly 339 bad tuples.";

    BadMatrix := Matrix(K,#BadFlat,9,&cat[ z : z in BadFlat ]);
    return <WReps,BadMatrix>;
end function;

FindDistanceAtLeastT_Hybrid := function(U,Data)
    WReps := Data[1];
    BadMatrix := Data[2];
    error if #WReps ne 94,
        "Incomplete W-orbit list: refusing to certify a negative result.";

    t0 := Cputime();
    printf "Checking all %o scalar-orbit representatives of 3-spaces W...\n",#WReps;
    for j in [1..#WReps] do
        has,x,actual := FindGoodTupleForW(U,WReps[j],BadMatrix);
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
        printf "Exhausted all %o scalar-orbit representatives of 3-spaces W.\n",tested;
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
    print "Exhaustive hybrid search for [6,1,3]_{3^6/3}";
    print "Defining polynomial:",DefiningPolynomial(F);
    print "Exact reductions: full tail dim(W)=3; scalar orbits on U and W; H-coset bad-set test.";

    Data := PrepareSearchData();

    // Both U and W run through the same scalar orbits of three-spaces.
    // Reuse the coverage-certified list rather than enumerating it twice.
    Reps := Data[1];
    error if #Reps ne 94, "Unexpected number of scalar orbits on 3-spaces.";
    printf "%o scalar-orbit representatives for U (same list as W).\n",#Reps;

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

/********************** THREE REPRODUCIBLE EXAMPLES **********************/
RunExamples := procedure()
    ValidateParameters();
    print "Field polynomial:",FieldPolynomial;
    g5 := [ F!1,a,a^2+a^4,F!0,F!0,F!0 ];
    x5 := [ F!0,a^5,a^3+a^4,F!1,a,a^2+a^4 ];
    actual5 := DistanceToCode(x5,g5);
    error if actual5 ne 5, "The explicit distance-5 witness failed.";
    print "Explicit generator g5:",g5;
    print "Explicit witness x5:",x5;
    print "Direct DistanceToCode(x5,g5):",actual5;

    // Direct certificate for the exact ordered generator in Section 4.3.
    gPaper := [ F!1, a^282, a^117, F!0, F!0, F!0 ];
    xPaper := [ F!0, a^4, 2*a^4+a^5, F!1, a, a^2+a^4 ];
    paperDistance := DistanceToCode(xPaper,gPaper);
    error if paperDistance ne 5, "The manuscript example certificate failed.";
    print "Manuscript generator:", gPaper;
    print "Manuscript example witness:", xPaper;
    print "Direct distance for the manuscript example:", paperDistance;

    Data := PrepareSearchData();
    Examples := [* [ F!1,a,a^2 ], [ F!1,a,a^2+a^4 ] *];
    Append(~Examples, [ F!1, a^282, a^117 ]); // Exact manuscript example.
    Expected := [ 4,5,5 ];
    for i in [1..#Examples] do
        U := UFromFieldElements(Examples[i]);
        printf "Example %o: expected rho=%o; now computing it.\n",i,Expected[i];
        PrintGeneratorFromU(U);
        has,x,W,actual,tested := FindDistanceAtLeastT_Hybrid(U,Data);
        ReportResult(has,x,W,actual,tested);
        rho := LowerRadius;
        if has then
            rho := TargetDistance;
        end if;
        error if rho ne Expected[i], "Example classification disagrees with expectation.";
    end for;
end procedure;

/********************** HOW TO RUN **********************/
// In a fresh Magma session:
//   load "check_cr_613_q3.m";
// The default AutoRun=true starts the complete search.
// For a batch, edit StartRep/EndRep at the top BEFORE loading.
// To check only the three examples, edit ExamplesOnly:=true IN THIS FILE before loading.
// To load without running anything, edit AutoRun:=false IN THIS FILE before loading;
// then call RunExamples(); or RunSearch(); explicitly.
//
// To test only one custom 3-space U, set AutoRun:=false, load, and enter e.g.
//   TestCustomU([ F!1, a, a^2 ]);
//
// The displayed generator uses an RREF basis of U and is normalized by
// its first entry.  Powers of a refer to THIS field's defining polynomial.
// Different source-field models must be matched by a field isomorphism.

if AutoRun then
    if ExamplesOnly then
        RunExamples();
    else
        RunSearch();
    end if;
end if;
