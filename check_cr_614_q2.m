/*
Purpose: Exact threshold test for one-dimensional rank-metric codes.
Parameters: q=2, m=6, n=6, k=1, minimum rank distance d=4.
Mathematical criterion: rk(x-lambda*g) = dim(W) + quotient tuple rank.
Expected output: 11 scalar orbits, all expected to have rho=4 (manuscript).
  WantWitness controls printing only; positive witnesses are always verified.
*/
/**********************************************************************
  check_cr_614_q2.m
  Exhaustive threshold test for [6,1,4]_{2^6/2} rank-metric codes.

  g = (u_1,...,u_d,0,...,0), dim_F2 <u_1,...,u_d> = d.
  We use the supplied theoretical fact rho(C) in {4,5}.
  This program decides whether a word of distance >= 5 exists.

  COMPLETENESS
  For a word x let W=<x_(d+1),...,x_n>, s=dim(W), pi:F_64 -> F_64/W.
  For every lambda,
    rk(x-lambda*g) = s + dim <pi(x_i)-pi(lambda*u_i):1<=i<=d>.
  Thus all possible witnesses occur among ALL W with
    max(0,T-d) <= s <= min(n-d,6).
  Conversely, lift any surviving quotient tuple, append a basis of W,
  and then append n-d-s zeros. The same identity proves its distance.

  NO ORBIT REDUCTION ON W IS USED.
  All subspaces of each required dimension are enumerated exactly once
  via their unique reduced row echelon matrices. The counts are checked.
  CheckDimensions must contain ALL required dimensions, exactly once;
  otherwise the program stops with an error, never a negative certificate.

  SAFE SCALAR REDUCTION ON U
  A basis change in U is a GL(d,2) right coordinate transformation,
  extended by the identity on the zero coordinates: a rank isometry.
  Replacing U by alpha*U additionally multiplies the generator by a
  nonzero scalar and leaves its F_64-span unchanged. Thus one U per
  scalar orbit suffices. No Frobenius reduction is used.

  COMPACT FORM OF THE SAME TRANSLATED-BAD-TUPLE TEST
  Write h=6-s and encode each d-tuple of F_2^h by one dh-bit integer.
  IsBad[z+1] records whether its component span has dimension < T-s.
  This table depends only on h,d,T-s, and is built once per dimension.
  Removing y when IsBad[(y XOR delta_lambda) + 1] is true is exactly
  marking the union of all translated bad tuples (parentheses in code).

  A further EXACT, optional optimization uses
    H = { (pi(lambda*u_1),...,pi(lambda*u_d)) : lambda in F_64 }.
  H is an F_2-subspace. The union Bad+H is H-invariant, so a complement
  of H in Q^d contains a good tuple iff Q^d contains one. Echelon pivots
  give this complement: set the pivot coordinates to zero and enumerate
  every choice on the remaining coordinates. Here s<d, so lambda*U
  cannot lie in W for nonzero lambda: dim(H)=6 and |H|=64.
  No W is discarded. UseTranslationReduction=false tests all tuples.

  Every positive result is reconstructed and independently verified by
  DistanceToCode, using 64 ordinary Magma subspace-rank computations.
  WantWitness controls PRINTING only; verification is always performed.

 
**********************************************************************/

/********************** PARAMETERS **********************/
q := 2;
m := 6;
n := 6;
d := 4;
TargetDistance := 5;
LowerRadius := 4;

StartRep := 1;
EndRep := 0;                       // 0 = last representative
StopAfterFirstRho5 := false;
StopAfterFirstRho4 := false;
WantWitness := true;              // false hides x; still verifies it
CheckDimensions := [ 2, 1 ];
UseTranslationReduction := true;  // exact reduction, proved above
ProgressEveryW := 50;             // 0 disables periodic W messages
ProgressEveryTable := 131072;     // 0 disables table progress messages
RunInternalChecks := true;        // counts, conversions, rank samples
AutoRun := true;                  // false = load functions only

/********************** FIELDS AND CONVERSIONS **********************/
// Exact sphere-covering lower bound, valid also when n > m.
AuditRankCount := function(rows,cols,r)
    num := 1;
    den := 1;
    for i in [0..r-1] do
        num *:= (q^rows-q^i)*(q^cols-q^i);
        den *:= q^r-q^i;
    end for;
    return num div den;
end function;
error if q^6 * (&+[ AuditRankCount(6,6,r) : r in [0..3] ]) ge q^36,
    "Sphere-covering check failed to certify the lower bound.";
error if q ne 2 or m ne 6 or n ne 6 or d ne 4,
    "This file is specialized to the parameters in its header.";

K := GF(q);
F<a> := GF(q^m);
V := VectorSpace(K,m);
print "Field defining polynomial:", DefiningPolynomial(F);
error if &or[ &+[ F!(Eltseq(z)[i])*a^(i-1) : i in [1..m] ] ne z : z in F ],
    "Polynomial-coordinate conversion failed.";


Vec := function(x)
    return V!Eltseq(F!x);
end function;

EltFromVec := function(v)
    return &+[ F!v[i]*a^(i-1) : i in [1..m] ];
end function;

// Little-endian binary encoding; all tuple indices below are ZERO based.
VectorIndex0 := function(v)
    c := Eltseq(v);
    return &+[ (Integers()!c[i])*2^(i-1) : i in [1..#c] ];
end function;

Bits := function(z,k)
    return [ K!((z div 2^j) mod 2) : j in [0..k-1] ];
end function;

FieldElements := [ EltFromVec(V!Bits(z,m)) : z in [0..2^m-1] ];

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

// Independent check: no quotient, integer-rank lookup, or coset reduction.
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
GaussianBinomial2 := function(k,s)
    num := 1;
    den := 1;
    for i in [0..s-1] do
        num *:= 2^k-2^i;
        den *:= 2^s-2^i;
    end for;
    return num div den;
end function;

SubspacesOfDimension := function(X,s)
    k := Dimension(X);
    error if Degree(X) ne k or #BaseRing(X) ne 2,
        "SubspacesOfDimension expects a full binary vector space.";
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
        for mask in [0..2^(#slots)-1] do
            M := ZeroMatrix(BaseRing(X),s,k);
            for i in [1..s] do
                M[i,piv[i]] := 1;
            end for;
            for j in [1..#slots] do
                M[slots[j][1],slots[j][2]] := (mask div 2^(j-1)) mod 2;
            end for;
            Append(~Subs,sub< X | [ X!M[i] : i in [1..s] ] >);
        end for;
    end for;
    error if #Subs ne GaussianBinomial2(k,s), "Subspace count mismatch.";
    return Subs;
end function;

// The membership bit mask is independent of the chosen basis of U.
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
        if SubspaceKey(U) notin Seen then
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

/********************** INDEXED BAD TUPLES **********************/
// Number of h-by-d binary matrices of rank exactly k.
RankMatrixCount2 := function(h,len,k)
    num := 1;
    den := 1;
    for i in [0..k-1] do
        num *:= (2^h-2^i)*(2^len-2^i);
        den *:= 2^k-2^i;
    end for;
    return num div den;
end function;

BuildBadTuplesData := function(h,len,NeedDim)
    error if NeedDim lt 1 or NeedDim gt Min(h,len), "Invalid rank threshold.";
    Qsize := 2^h;
    Total := Qsize^len;
    IsBad := [ false : j in [1..Total] ];
    // Hi[z+1] = position (1 based) of the highest nonzero bit of z.
    Hi := [ 0 : j in [1..Qsize] ];
    for j in [1..h] do
        for z in [2^(j-1)..2^j-1] do
            Hi[z+1] := j;
        end for;
    end for;
    BadCount := 0;
    t0 := Cputime();
    for idx in [0..Total-1] do
        work := idx;
        pivot := [ 0 : j in [1..h] ];
        rk := 0;
        for col in [1..len] do
            z := work mod Qsize;
            work := work div Qsize;
            while z ne 0 do
                p := Hi[z+1];
                if pivot[p] eq 0 then
                    pivot[p] := z;
                    rk +:= 1;
                    break;
                end if;
                z := BitwiseXor(z,pivot[p]);
            end while;
            if rk ge NeedDim then
                break;
            end if;
        end for;
        IsBad[idx+1] := rk lt NeedDim;
        if IsBad[idx+1] then
            BadCount +:= 1;
        end if;
        if ProgressEveryTable gt 0 then
            if (idx+1) mod ProgressEveryTable eq 0 then
                printf "  Rank table: %o/%o; CPU %o s\n", idx+1,Total,Cputime(t0);
            end if;
        end if;
    end for;
    expected := &+[ RankMatrixCount2(h,len,k) : k in [0..NeedDim-1] ];
    error if BadCount ne expected, "Bad-tuple count mismatch.";
    if RunInternalChecks then
        // Deterministic samples checked using ordinary Magma matrix rank.
        samples := { (j*104729) mod Total : j in [0..255] };
        samples join:= { j : j in [0..Min(255,Total-1)] };
        for idx in samples do
            M := Matrix(K,len,h,Bits(idx,h*len));
            error if IsBad[idx+1] ne (Rank(M) lt NeedDim),
                "Integer rank table disagrees with Magma Rank.";
        end for;
    end if;
    printf "  h=%o, NeedDim=%o: %o indices, %o bad; CPU %o s\n",
        h,NeedDim,Total,BadCount,Cputime(t0);
    return IsBad;
end function;

TupleIndex0 := function(L,h)
    return &+[ VectorIndex0(L[i])*2^(h*(i-1)) : i in [1..#L] ];
end function;

// Complement to the binary span of all shifts; an EXACT transversal.
TranslationTransversal := function(Shifts,nbits)
    M := Matrix(K,#Shifts,nbits,&cat[ Bits(z,nbits) : z in Shifts ]);
    E := EchelonForm(M);
    piv := [ Integers() | ];
    for i in [1..Nrows(E)] do
        for j in [1..nbits] do
            if E[i,j] ne 0 then
                Append(~piv,j);
                break;
            end if;
        end for;
    end for;
    // Injectivity follows from s<d in each of the three requested cases.
    error if #piv ne m, "The translation subspace should have dimension 6.";
    Free := [ j : j in [1..nbits] | j notin piv ];
    Reps := [ Integers() | 0 ];
    for j in Free do
        Reps := Reps cat [ z+2^(j-1) : z in Reps ];
    end for;
    error if #Reps*#Shifts ne 2^nbits, "Transversal size mismatch.";
    return Reps;
end function;

/********************** ONE W AND RECONSTRUCTION **********************/
// Results: hasWitness, x, independently computed distance.
FindGoodTupleForW := function(U,W,IsBad,ReduceTranslations)
    s := Dimension(W);
    h := m-s;
    Q,pi := quo< V | W >;
    error if Dimension(Q) ne h or Degree(Q) ne h,
        "The quotient must use h standard coordinates.";
    error if #IsBad ne 2^(h*d), "Wrong lookup-table size.";
    B := BasisElements(U);
    Shifts := [ TupleIndex0([ pi(Vec(lambda*u)) : u in B ],h)
                : lambda in FieldElements ];
    error if #Seqset(Shifts) ne 64, "Translation injectivity check failed.";
    if ReduceTranslations then
        Survivors := TranslationTransversal(Shifts,h*d);
    else
        Survivors := [ Integers() | 0..2^(h*d)-1 ];
    end if;

    // This computes the complement of the union of translated bad sets.
    // Discarded entries never need to be tested again.
    for shift in Shifts do
        Survivors := [ z : z in Survivors | not IsBad[BitwiseXor(z,shift)+1] ];
        if #Survivors eq 0 then
            return false,[ F | ],-1;
        end if;
    end for;

    // Build a section of pi by enumerating only the 64 field elements.
    // No @@ operation or assumption on how Magma lifts quotient vectors.
    Lift := [ F!0 : j in [1..2^h] ];
    Assigned := [ false : j in [1..2^h] ];
    for z in FieldElements do
        j := VectorIndex0(pi(Vec(z)))+1;
        if not Assigned[j] then
            Lift[j] := z;
            Assigned[j] := true;
        end if;
    end for;
    error if not (&and Assigned), "Quotient section is not surjective.";
    idx := Survivors[1];
    x := [ F | ];
    for j in [1..d] do
        Append(~x,Lift[(idx mod 2^h)+1]);
        idx := idx div 2^h;
    end for;
    x := x cat BasisElements(W) cat [ F!0 : j in [1..n-d-s] ];
    error if #x ne n, "Witness has the wrong length.";
    actual := DistanceToCode(x,MakeGenerator(U));
    error if actual lt TargetDistance, "Independent witness verification FAILED.";
    error if actual gt TargetDistance,
        "Witness contradicts the supplied theoretical upper bound.";
    return true,x,actual;
end function;

/********************** PRECOMPUTATION AND COMPLETE SEARCH **********************/
RequiredDimensions := [ Max(0,TargetDistance-d)..Min(m,n-d) ];

ValidateParameters := procedure()
    error if q ne 2 or m ne 6, "These scripts are specialized to F_64/F_2.";
    error if n ne 6 or d ne 4 or TargetDistance ne 5 or LowerRadius ne 4,
        "Do not change the fixed code parameters of this file.";
    error if Seqset(CheckDimensions) ne Seqset(RequiredDimensions)
        or #CheckDimensions ne #RequiredDimensions,
        "CheckDimensions must list ALL required dimensions exactly once.";
    error if StartRep lt 1 or EndRep lt 0, "Invalid batch parameters.";
    error if ProgressEveryW lt 0 or ProgressEveryTable lt 0,
        "Progress intervals must be nonnegative.";
    if RunInternalChecks then
        error if #Seqset(FieldElements) ne 64, "Field enumeration failed.";
        for j in [1..64] do
            error if EltFromVec(Vec(FieldElements[j])) ne FieldElements[j]
                or VectorIndex0(Vec(FieldElements[j])) ne j-1,
                "Field/vector conversion failed.";
        end for;
    end if;
end procedure;

// Each entry is <dimension, ALL W of that dimension, bad-rank lookup>.
PrepareSearchData := function()
    ValidateParameters();
    Data := [* *];
    for s in CheckDimensions do
        t0 := Cputime();
        WList := SubspacesOfDimension(V,s);
        if RunInternalChecks then
            error if #{ SubspaceKey(W) : W in WList } ne #WList,
                "Duplicate W in RREF enumeration.";
        end if;
        printf "All W with dim %o: %o; enumeration CPU %o s\n",s,#WList,Cputime(t0);
        IsBad := BuildBadTuplesData(m-s,d,TargetDistance-s);
        Append(~Data,<s,WList,IsBad>);
    end for;
    return Data;
end function;

FindDistanceAtLeastT_Hybrid := function(U,Data)
    // Prevent an incomplete externally supplied Data list being certified.
    error if #Data ne #RequiredDimensions
        or { D[1] : D in Data } ne Seqset(RequiredDimensions),
        "Incomplete search data: refusing to certify a negative result.";
    tested := 0;
    for D in Data do
        s := D[1];
        WList := D[2];
        error if #WList ne GaussianBinomial2(m,s), "Incomplete W list.";
        error if &or[ Dimension(W) ne s : W in WList ], "Wrong W dimension.";
        error if #{ SubspaceKey(W) : W in WList } ne #WList,
            "Duplicate W: refusing to certify an incomplete search.";
        t0 := Cputime();
        printf "Checking ALL %o subspaces W of dimension %o...\n",#WList,s;
        for j in [1..#WList] do
            has,x,actual := FindGoodTupleForW(U,WList[j],D[3],UseTranslationReduction);
            tested +:= 1;
            if has then
                printf "  Found at W %o/%o; CPU %o s\n",j,#WList,Cputime(t0);
                return true,x,WList[j],actual,tested;
            end if;
            if ProgressEveryW gt 0 then
                if j mod ProgressEveryW eq 0 then
                    printf "  Checked W %o/%o; CPU %o s\n",j,#WList,Cputime(t0);
                end if;
            end if;
        end for;
        printf "  Finished all %o W of dimension %o; CPU %o s\n",#WList,s,Cputime(t0);
    end for;
    expected := &+[ GaussianBinomial2(m,s) : s in RequiredDimensions ];
    error if tested ne expected, "Incomplete negative certificate.";
    return false,[ F | ],sub< V | [] >,-1,tested;
end function;

ReportResult := procedure(has,x,W,actual,tested)
    if has then
        printf "Result: rho(C) = %o.\n",TargetDistance;
        printf "Independent DistanceToCode(x,g) = %o (all 64 scalars).\n",actual;
        print "Basis of W:",BasisElements(W);
        if WantWitness then
            print "Witness x:",x;
        end if;
    else
        printf "Exhausted ALL %o required W; no quotient tuple survives.\n",tested;
        printf "Certified: rho(C) <= %o.\n",TargetDistance-1;
        printf "Using the sphere-covering lower bound: rho(C) = %o.\n",LowerRadius;
    end if;
end procedure;

TestCustomU := procedure(L)
    ValidateParameters();
    U := UFromFieldElements([ F!z : z in L ]);
    error if Dimension(U) ne d, "The supplied elements have the wrong span dimension.";
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
    print "Exhaustive hybrid search for [6,1,4]_{2^6/2}";
    print "Defining polynomial:",DefiningPolynomial(F);
    print "CheckDimensions:",CheckDimensions;
    print "Exact tuple-translation reduction:",UseTranslationReduction;
    Data := PrepareSearchData();
    t0 := Cputime();
    AllU := SubspacesOfDimension(V,d);
    Reps := ScalarOrbitRepresentatives(AllU);
    printf "%o U subspaces; %o scalar-orbit representatives; CPU %o s\n",
        #AllU,#Reps,Cputime(t0);
    // Counts from the stabilizers F_2^*, F_4^* (d=4), F_8^* (d=3).
    expectedReps := 11;
    error if #Reps ne expectedReps, "Unexpected number of scalar orbits.";
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
        if (rho eq 5 and StopAfterFirstRho5)
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
    if #Results eq #Reps and StartRep eq 1 then
        print "ALL scalar-orbit representatives classified.";
    else
        print "Only the listed representatives were classified (batch/early stop).";
        print "No conclusion is made for unprocessed U representatives.";
    end if;
    printf "Total CPU: %o s\n",Cputime(totalTime);
end procedure;

/********************** HOW TO RUN **********************/
// In a fresh Magma session:
//   load "check_cr_614_q2.m";
// The default AutoRun=true starts the complete search.
// For a batch, edit StartRep/EndRep at the top BEFORE loading.
// To test a custom U, set AutoRun:=false at the top, load, and enter:
//   TestCustomU([ F!1, a, a^2, a^3 ]);
// This tests the span; MakeGenerator may replace your basis by an RREF
// basis. The witness printed belongs to the displayed code. The displayed
// normalized generator differs from MakeGenerator(U) only by a scalar.
// Powers of a refer to THIS field's printed defining polynomial.
// Different source-field models must be matched by a field isomorphism.

if AutoRun then
    RunSearch();
end if;
