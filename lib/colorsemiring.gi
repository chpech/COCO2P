DeclareRepresentation( "IsColorSemiringElementRep", 
        IsPositionalObjectRep,
        [1]);

InstallMethod( ViewString,
    "for elements of color semirings",
    [ IsElementOfColorSemiring and IsColorSemiringElementRep ],
    function( obj )
    return Concatenation("<", String(obj![1]), ">" );
end );

InstallMethod( ViewString,
        "for color semirings",
        [IsColorSemiring],
function(sr)
    return "<ColorSemiring>";
end);

InstallMethod( ColorSemiringElement,
        "for a family of color semiring elements and a set of colors",
        [IsElementOfColorSemiringFamily, IsList],
function( Fam, set )
    return Objectify( NewType( Fam, IsElementOfColorSemiring and IsColorSemiringElementRep ),
                   [ Set(set) ] );
end );

InstallMethod( \=,
        "for two color semiring elements",
        IsIdenticalObj,
        [ IsElementOfColorSemiring and IsColorSemiringElementRep,
          IsElementOfColorSemiring and IsColorSemiringElementRep ],
function( a, b )
    return a![1] = b![1];
end );

InstallMethod( \<,
        "for two color semiring elements",
        IsIdenticalObj,
        [ IsElementOfColorSemiring and IsColorSemiringElementRep,
          IsElementOfColorSemiring and IsColorSemiringElementRep ],
function( a, b )
    return a![1] < b![1];
end );

InstallGlobalFunction( ColorSemiring, 
function( cgr )
    local fam, sr, gens;
 
 
    # Construct the family of element objects of our semiring.
    fam:= NewFamily( "ColorSemiringElementsFam",
                  IsElementOfColorSemiring and 
                  IsAssociativeElement and 
                  IsAdditivelyCommutativeElement,IsObject, IsElementOfColorSemiringFamily );
 
    # Install the data.
    fam!.cgr:= cgr;
    fam!.tensor:=StructureConstantsOfColorGraph(cgr);
    
    # Make the domain.
    gens:=List([1..OrderOfTensor(fam!.tensor)], i->ColorSemiringElement( fam, [i] )  );
    sr:=Objectify( NewType( CollectionsFamily(fam) ,
                            IsColorSemiring and IsAttributeStoringRep ),
                   rec() );

    SetIsWholeFamily( sr, true );
    SetGeneratorsOfAdditiveMagmaWithZero( sr, gens );
    SetRepresentative( sr, gens[1]);
    
    # Return the colorsemiring.
    return sr;
end );

InstallMethod(GeneratorsOfColorSemiring,
        "for color semirings",
        [IsColorSemiring and HasGeneratorsOfAdditiveMagmaWithZero],
        GeneratorsOfAdditiveMagmaWithZero);


InstallMethod( OneOp,
        "for color semiring elements",
        [IsElementOfColorSemiring],
function(elm)
    local fam,tensor;
    fam:=FamilyObj(elm);
    tensor:=fam!.tensor;
    return ColorSemiringElement( fam, Set(ReflexiveColors(tensor)));
end);

InstallMethod( ZeroOp,
        "for color semiring elements",
        [IsElementOfColorSemiring],
elm->ColorSemiringElement( FamilyObj(elm), []));

InstallMethod( \*,
        "for two color semiring elements",
        IsIdenticalObj,
        [ IsElementOfColorSemiring and IsColorSemiringElementRep,
          IsElementOfColorSemiring and IsColorSemiringElementRep ],
function( a, b )
    local fam, vec;
    fam:=FamilyObj(a);
    vec:=ComplexProduct(fam!.tensor,a![1], b![1]);
    return ColorSemiringElement(fam, Filtered([1..Length(vec)], i->vec[i]<>0));
end );

InstallMethod( \*,
        "for a vertex and a color semiring element",
        [ IsPosInt, IsElementOfColorSemiring and IsColorSemiringElementRep ],
function( v, b )
    local fam, cgr;
    fam:=FamilyObj(b);
    cgr:=fam!.cgr;
    if v>OrderOfColorGraph(cgr) then
        Error("Not a vertex!");
    fi;
    return Neighbors(cgr,v,AsSet(b));
end);

InstallOtherMethod( \*,
        "for a vertex and a color semiring element",
        [ IsList, IsElementOfColorSemiring and IsColorSemiringElementRep ],
function( v, b )
    local fam, cgr;
    fam:=FamilyObj(b);
    cgr:=fam!.cgr;
    return Union(Set(v, x->x*b));
end);

InstallMethod( \*,
        "for a color semiring element and a vertex",
        [ IsElementOfColorSemiring and IsColorSemiringElementRep, IsPosInt ],
function( b, v )
    local fam, cgr;
    fam:=FamilyObj(b);
    cgr:=fam!.cgr;
    if v>OrderOfColorGraph(cgr) then
        Error("Not a vertex!");
    fi;
    return Neighbors(cgr,v,OnSets(AsSet(b),ColorMates(cgr)));
end);

InstallOtherMethod( \*,
        "for a vertex and a color semiring element",
        [  IsElementOfColorSemiring and IsColorSemiringElementRep, IsList ],
function( b, v )
    local fam, cgr;
    fam:=FamilyObj(b);
    cgr:=fam!.cgr;
    return Union(Set(v, x->b*x));
end);

InstallMethod( \+,
        "for two color semiring elements",
        IsIdenticalObj,
        [ IsElementOfColorSemiring and IsColorSemiringElementRep,
          IsElementOfColorSemiring and IsColorSemiringElementRep ],
function(a,b)
    return ColorSemiringElement(FamilyObj(a), Union(a![1],b![1]));
end);

InstallGlobalFunction(AsElementOfColorSemiring,
function(sr,set)
    local fam,tensor;
    
    fam:=ElementsFamily(FamilyObj(sr));
    tensor:=fam!.tensor;
    if not IsSubset([1..OrderOfTensor(tensor)],set) then
        Error("The given set is not a set of colors!");
    fi;
    return ColorSemiringElement(fam, set);
end);

InstallOtherMethod(AsSet,
        "for color semiring elements",
        [IsElementOfColorSemiring and IsColorSemiringElementRep],
function(elm)
    return elm![1];
end);

InstallMethod(\^,
        "for color semiring elements and permutations",
        [IsElementOfColorSemiring and IsColorSemiringElementRep, IsPerm],
function(elm,g)
    local   fam,  tensor,  set,  nset;
    
    fam:=FamilyObj(elm);
    tensor:=fam!.tensor;
    set:=elm![1];
    nset:=OnSets(set,g);
    if not IsSubset([1..OrderOfTensor(tensor)],nset) then
        Error("The given permutation does not act on colors!");
    fi;
    
    return ColorSemiringElement(fam,nset);
end);

