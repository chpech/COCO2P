
InstallGlobalFunction(MyValue,
function(poly, indet, value)
    if not IsPolynomial(poly) then
        return poly;
    fi;
    return Value(poly, [indet],[value]);
end);

if TestPackageAvailability("alnuth","3")=true and AL_EXECUTABLE<>fail then
    Print("COCO2P: Using Alnuth and PARI/GP to for factorizing polynomials...\n");
    
    FactorsOfAlgebraicUPol:=function(poly)
        local  F, x, a, minpol, L, b, basisF, basisL, coeffs, y, cpoly, 
               factors, fcoeffs;

        F:=FieldOfPolynomial(poly);
        x:=IndeterminateOfUnivariateRationalFunction(poly);
        a:=PrimitiveElement(F);
        minpol:=MinimalPolynomial(Rationals,a);
        L:=FieldByPolynomial(minpol);
        b:=RootOfDefiningPolynomial(L);
        basisF:=Basis(F,List([0..Dimension(AsVectorSpace(Rationals,F))-1], i->a^i));
        basisL:=Basis(L,List([0..Dimension(AsVectorSpace(Rationals,L))-1], i->b^i));
        coeffs:=CoefficientsOfUnivariatePolynomial(poly);
        coeffs:=List(coeffs, c->LinearCombination(basisL,Coefficients(basisF,c)));
        y:=Indeterminate(L,"y");
        cpoly:=UnivariatePolynomial(L, coeffs,y);

        factors:=FactorsPolynomialPari(cpoly);
        fcoeffs:=List(factors, p->CoefficientsOfUnivariatePolynomial(p));
        fcoeffs:=List(fcoeffs, cf->
                      List(cf, c->LinearCombination(basisF,Coefficients(basisL,c))));
        factors:=List(fcoeffs, cf->UnivariatePolynomial(F,cf,x));
        return factors;
    end;

    RootsOfRationalUPol:=function(q,poly)
        local  x,L, y, factors, roots, a, basisL, vecs, CFq,dim;

        x:=IndeterminateOfUnivariateRationalFunction(poly);
        L:=FieldByPolynomial(CyclotomicPolynomial(Rationals,q));
        dim:=Dimension(L);
        if dim>1 then
            a:=RootOfDefiningPolynomial(L);
            y:=Indeterminate(L,"y");
        else
            y:=x;
            a:=1;
        fi;

        factors:=FactorsPolynomialAlgExt(L,poly);
        factors:=Filtered(factors, p->Degree(p)=1);

        roots:=List(factors, x->-Value(x,[y], [Zero(L)])/LeadingCoefficient(x));
        basisL:=Basis(L,List([0..dim-1], i->a^i));
        vecs:=List(roots, r->Coefficients(basisL,r));
        CFq:=CyclotomicField(q);
        roots:=List(vecs, v->Sum([0..dim-1], i->v[i+1]*E(q)^i));
        Info(InfoTensor,2,"Input Polynomial: ", poly);
        Info(InfoTensor,2,"factors: ", factors);
        Info(InfoTensor,2,"roots: ", roots);

        return roots;
    end;
    InstallGlobalFunction(MyRootsOfPoly,
            function(poly)
        local  roots, indet, F, lpolys, p, discriminant, 
               factors, degrees, f, n, rtp, i;

        if Degree(poly)<=1 then 
            return RootsOfUPol(poly);
        fi;

        roots := [];
        indet := IndeterminateOfUnivariateRationalFunction(poly);
        Info(InfoTensor, 1, "finding roots of polynomial ", poly);
        F:=FieldOfPolynomial(poly);
        if F<>Rationals then
            lpolys:= FactorsOfAlgebraicUPol(poly);
        else
            lpolys:=[poly];
        fi;

        for p in lpolys do
            discriminant:=Discriminant(p);
            Info(InfoTensor, 2, "discriminant: ", discriminant);
            if discriminant=1 then
                rtp:=RootsOfUPol(p);
                Info(InfoTensor,2, "roots of ", p, " are: ", rtp);
                
                Append(roots, rtp);
                continue;
            fi;
            
            factors := Filtered(DivisorsInt(Sqrt(discriminant*ComplexConjugate(discriminant))), IsPrimePowerInt);
            Info(InfoTensor, 2, "factors of discriminant: ", factors);
            #        degrees := Concatenation(factors, Difference(degrees, factors));
            f:=FieldOfPolynomial(p)=Rationals;

            for n in factors do
                Info(InfoTensor, 2, "looking in CF(", n, ")");
                if f then
                    Info(InfoTensor,2, "roots of rational poly ", p);

                    rtp:=RootsOfRationalUPol(n,p);
                else
                    Info(InfoTensor,2, "roots of algebraic poly ", p);
                    rtp:=RootsOfUPol(CF(n),p);
                fi;

                for i in rtp do
                    Add(roots, i);

                    p := p/(indet-i);
                od;
                if DegreeOfLaurentPolynomial(p) <= 0 then
                    break;
                fi;
            od;
        od;
        Info(InfoTensor, 1, "done");
        return roots;
    end);
else
    InstallGlobalFunction(MyRootsOfPoly,
            function(poly)
        local   F, roots,  indet,  i,  n, degrees,  factors, discriminant,coeffs;
        roots := [];
        indet := IndeterminateOfUnivariateRationalFunction(poly);
        Info(InfoTensor, 1, "finding roots of polynomial ", poly);
        for i in RootsOfUPol(poly) do
            Add(roots, i);
            poly := poly/(indet-i);
        od;
        if DegreeOfLaurentPolynomial(poly) <= 0 then
            Info(InfoTensor, 1, "done");
            return roots;
        fi;
#        degrees := [2..20];
#        discriminant := Discriminant(poly);
#        Info(InfoTensor, 2, "discriminant: ", discriminant);
#        factors := Filtered(DivisorsInt(Sqrt(discriminant*ComplexConjugate(discriminant))), IsPrimePowerInt);
#        factors := DivisorsInt(Sqrt(discriminant*ComplexConjugate(discriminant)));
#        Info(InfoTensor, 2, "factors of discriminant: ", factors);
#        degrees := Concatenation(factors, Difference(degrees, factors));
        n:=1;
        while true do
#        for n in degrees do
            Info(InfoTensor, 2, "looking in CF(", n, ")");
            coeffs:=CoefficientsOfLaurentPolynomial(poly)[1];
            if ForAny(coeffs, x->not x in CF(n)) then
                n:=n+1;
                
                continue;
            fi;
            
            
            for i in RootsOfUPol(CF(n), poly) do
                Add(roots, i);

                poly := poly/(indet-i);
            od;
            if DegreeOfLaurentPolynomial(poly) <= 0 then
                break;
            fi;
            n:=n+1;
        od;
        if DegreeOfLaurentPolynomial(poly)>1 then
            Error("not completely factorized");
        fi;
        
        Info(InfoTensor, 1, "done");
        return roots;
    end);
fi;


InstallGlobalFunction(CharacteristicSystem,
function(tensor)
    local   system,  ring,  indets,  i,  j,  poly,  result;

    system := [];
    ring := PolynomialRing( Rationals, Order(tensor));
    indets := IndeterminatesOfPolynomialRing(ring);
    for i in [1..Order(tensor)] do
        for j in [i..Order(tensor)] do
            poly := indets[i]*indets[j];
            poly := poly - Sum([1..Order(tensor)], k ->
                            indets[k] * EntryOfTensor(tensor, i, j, k));
            Add(system, poly);
        od;
    od;
    Info( InfoTensor, 1, "computing Groebner basis...");
    result :=  ReducedGroebnerBasis@(system, MonomialLexOrdering());
    Info(  InfoTensor, 1, "done" );
    return result;
end);

InstallGlobalFunction(SolutionsOfSystem,
function(system)
    local   eqn,  roots,  x,  i,  newSystem,  sols,  j, solutions;
    
    for i in [1..Length(system)] do # work around
        if IsRationalFunction(system[i]) and
           IsConstantRationalFunction(system[i]) then
            system[i] := Value(system[i], 0);
        fi;
    od;
    
    eqn := First(system, x -> x <> 0);
    if eqn = fail then
        return [[]];
    fi;
    if not IsPolynomial(eqn) then
        return [];
    fi;
    solutions := [];
    roots := MyRootsOfPoly( eqn);
    #Print("roots of ", eqn, ": ", roots, "\n");
    x := IndeterminateOfUnivariateRationalFunction(eqn);
    for i in roots do
        newSystem := List(system, poly -> MyValue(poly, x, i));
        sols := SolutionsOfSystem(newSystem);
        for j in sols do
            Add(solutions, Concatenation(j, [i]));
        od;
    od;
    #Print("returning solutions ", solutions, "\n");
    return solutions;
end);

# InstallGlobalFunction(MultiplicitiesOfCharacters,
# function(t, solutions)
#     local   A,  mates,  order,  rhs, ident;
    
#     ident:=ReflexiveColors(t)[1];
    
#     A := TransposedMat(solutions)^-1;
#     mates := Mates(t);
#     rhs := List([1..Order(t)], x -> 0);
#     rhs[ident] := Order(t);
#     return A*rhs;
# end);


InstallMethod( FirstEigenmatrix,
        "for commutative structure constants tensors",
        [IsTensor and IsCommutativeTensor and IsTensorOfCC],
function(t)
    local  system, solutions;
    system := CharacteristicSystem(t);
    solutions := SolutionsOfSystem(system);
    solutions := Filtered(solutions, x -> ForAny(x, y -> y <> 0));
    MakeImmutable(solutions);
    return solutions;
end);

InstallMethod( SecondEigenmatrix,
        "for commutative structure constants tensors",
        [IsTensor and IsCommutativeTensor and IsTensorOfCC],
function(t)
    local  P, n, Q;
    P:=FirstEigenmatrix(t);
    n:=Sum(FibreLengths(t));
    Q:=n*Inverse(P);
    MakeImmutable(Q);
    return Q;
end);

InstallMethod( CharacterTableOfTensor,
        "for commutative structure constants tensors",
        [IsTensor and IsCommutativeTensor and IsTensorOfCC],
function(t)
    local  r, P, Q, table;
    r:=ReflexiveColors(t)[1];
    P:=FirstEigenmatrix(t);
    Q:=SecondEigenmatrix(t);
    table := rec(
                  characters := P,
                  multiplicities := Q[r]);
    MakeImmutable(table);
    return table;
end);

InstallOtherMethod( CharacterTable,
        "for commutative structure constants tensors",
        [IsTensor and IsCommutativeTensor and IsTensorOfCC],
function(t)
    return CharacterTableOfTensor(t);
end);

InstallMethod( TensorOfKreinNumbers,
        "for commutative structure constants tensors",
        [IsTensor and IsCommutativeTensor and IsTensorOfCC],
function(tensor)
    local  n, P, Q, entries, i, j, k, val;
    
    n:=Sum(OutValencies(tensor));
    P:=FirstEigenmatrix(tensor);
    Q:=SecondEigenmatrix(tensor);
    entries:=List([1..Length(P)], i->List([1..Length(P)], j->List([1..Length(P)],k->0)));
    for i in [1..Length(P)] do
        for j in [1..Length(P)] do
            for k in [1..Length(P)] do
                val:=1/n*Sum(List([1..Length(P)], l->Q[l][i]*Q[l][j]*P[k][l]));
                entries[i][j][k]:=val;
            od;
        od;
    od;
    return DenseTensorFromEntries(entries);
end);

InstallMethod( IndexOfPrincipalCharacter,
        "for commutative structure constants tensors",
        [IsTensor and IsCommutativeTensor and IsTensorOfCC],
function(tensor)
    local  P, pc;
    P:=FirstEigenmatrix(tensor);
    pc:=OutValencies(tensor);
    return Position(P,pc);
end);

InstallMethod( QPolynomialOrdering,
        "for commutative structure constants tensors and a positive integer",
        [IsTensor and IsCommutativeTensor and IsTensorOfCC, IsPosInt],
function(tensor,i)
    local  krein, list, j, set, new;
    
    krein:=TensorOfKreinNumbers(tensor);
    list:=[IndexOfPrincipalCharacter(tensor),i];
    if Length(Set(list))<2 then
        return fail;
    fi;
    
    for j in [2..Order(krein)-1] do
        set:=Filtered([1..Order(krein)], k->EntryOfTensor(krein,list[j],i,k)<>0);
        new:=Difference(set, Set([list[j-1],list[j]]));
        if Length(new)<>1 then
            return fail;
        fi;
        list[j+1]:=new[1];
    od;
    return list;
end);

InstallMethod( QPolynomialOrderings,
        "for structure constants tensors",
        [IsTensor and IsTensorOfCC],
function(tensor)
    local  res;
    
    if not IsCommutativeTensor(tensor) then
        return [];
    fi;
    res:=List([1..Order(tensor)], i->QPolynomialOrdering(tensor,i));
    res:=Filtered(res, x->x<>fail);
    return res;
end);
