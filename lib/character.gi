
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
            
            factors := Filtered(DivisorsInt(discriminant), IsPrimePowerInt);
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
        local   F, roots,  indet,  i,  n, degrees,  factors, discriminant;
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
        degrees := [2..20];
        discriminant := Discriminant(poly);
        Info(InfoTensor, 2, "discriminant: ", discriminant);
        factors := Filtered(DivisorsInt(discriminant), IsPrimePowerInt);
        Info(InfoTensor, 2, "factors of discriminant: ", factors);
        degrees := Concatenation(factors, Difference(degrees, factors));
        for n in degrees do
            Info(InfoTensor, 2, "looking in CF(", n, ")");
            for i in RootsOfUPol(CF(n), poly) do
                Add(roots, i);

                poly := poly/(indet-i);
            od;
            if DegreeOfLaurentPolynomial(poly) <= 0 then
                break;
            fi;
        od;

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

InstallGlobalFunction(MultiplicitiesOfCharacters,
function(t, solutions)
    local   A,  mates,  order,  rhs, ident;
    
    ident:=ReflexiveColors(t)[1];
    
    A := TransposedMat(solutions)^-1;
    mates := Mates(t);
    rhs := List([1..Order(t)], x -> 0);
    rhs[ident] := Order(t);
    return A*rhs;
end);

InstallOtherMethod( CharacterTable,
        "for tensors",
        [IsTensor and IsCommutativeTensor],
function(t)
    return CharacterTableOfTensor(t);
end);


InstallMethod( CharacterTableOfTensor,
        "for tensors",
        [IsTensor and IsCommutativeTensor],
function(t)
    local   system,  solutions,  table,  A,  mates,  order,  rhs;
    system := CharacteristicSystem(t);
    solutions := SolutionsOfSystem(system);
    solutions := Filtered(solutions, x -> ForAny(x, y -> y <> 0));
    table := rec();
    table.characters := solutions;
    table.multiplicities := MultiplicitiesOfCharacters(t, solutions);
    return table;
end);
