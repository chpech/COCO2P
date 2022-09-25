############################################################################
##
##  subiso.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of SubColorIsomorphism tests and posets
##
############################################################################
# returns the list of all fusion orbits (under the known color
# automorphism group of cgr1) that are color isomorphic to cgr2
InstallMethod( OrbitsOfColorIsomorphicFusions,
        "for two homogeneous WL-stbale color graphs",
        [IsColorGraph and IsWLStableColorGraph, 
         IsColorGraph and IsWLStableColorGraph and IsHomogeneous],
function(cgr1,cgr2)
    local  lgs, t1, t2, sparams, aparams, c, lbd, k, llgs, p, lfus, 
           aaut, caut, res, fus, cgr;
    
    if Order(cgr1) <> Order(cgr2) then
        return [];
    fi;
    
    lgs:=[];
    
    t1:=StructureConstantsOfColorGraph(cgr1);
    t2:=StructureConstantsOfColorGraph(cgr2);
    
    sparams:=[];
    aparams:=[];
    
    for c in Difference([1..Rank(cgr2)],ReflexiveColors(cgr2)) do
        lbd:=t2[[c,c,c]];
        k:=OutValencies(cgr2)[c];
        
        if c^Mates(t2)<c then
            continue;
        fi;
            
        if c^Mates(t2)=c then
            AddSet(sparams,[k,lbd]);
        else
            AddSet(aparams,[k,lbd]);
            llgs:=HomogeneousAsymGoodSetOrbitsWithParameters(t1,k,lbd);
        fi;
    od;
    for p in sparams do
        llgs:=HomogeneousSymGoodSetOrbitsWithParameters(t1,p[1],p[2]);
            
        if llgs=[] then
            return [];
        fi;
        UniteSet(lgs,llgs);
    od;
        
    for p in aparams do
        llgs:=HomogeneousAsymGoodSetOrbitsWithParameters(t1,p[1],p[2]);
            
        if llgs=[] then
            return [];
        fi;
        UniteSet(lgs,llgs);
    od;
    
    lfus:=FusionOrbitsFromGoodSetOrbits(lgs);
    lfus:=Filtered(lfus, x->RankOfFusion(Representative(x))=Rank(cgr2));
    
    aaut:=AutomorphismGroup(t1);
    caut:=ColorAutomorphismGroupOnColors(cgr1);
    if caut<>aaut then
        lfus:=Concatenation(List(lfus, x->SubOrbitsOfCocoOrbit(caut,x)));
    fi;
    
    res:=[];
    
    for fus in lfus do 
        cgr:=ColorGraphByFusion(cgr1,Representative(fus));
        if IsColorIsomorphicColorGraph(cgr,cgr2) then
            Add(res, fus);
        fi;
    od;
    
    return res;
end);

DeclareRepresentation( "IsSubColorIsomorphismPosetRep",
        IsCocoPosetRep,
        ["elements",     # list of all elements of the poset. The list must be
                         # ordered in a way that is compatible with the partial
                         # order relation (no element is preceeded by a greater element).
         "successors",   # on index i the list of all indices of successors of the
                         # element #i is stored
         "predecessors", # the same as successors for predecessors
         "mergings"      # if order(x,y)=true, then mergings[y][x] contains the fusions
                         # of elements[y] that are color isomorphic to elements[x]
         ]);

InstallGlobalFunction(SubColorIsomorphismPoset,
function(lW)
    local mergings,order,linorder,poset;

    order:=function(y,x)
        local info;

        info:=OrbitsOfColorIsomorphicFusions(lW[x],lW[y]);
        if info<>[] then
            if not IsBound(mergings[x]) then
                mergings[x]:=[];
            fi;

            mergings[x][y]:=info;
            return true;
        else
            return false;
        fi;
    end;

    linorder:=function(x,y)
        return Rank(lW[x])<Rank(lW[y]);
    end;

    mergings:=[];

    poset:=CocoPosetByFunctions([1..Length(lW)],order,linorder);

    poset!.mergings:=Immutable(mergings);
    poset!.elements:=Immutable(List(poset!.elements, i->lW[i]));
    SetFilterObj(poset,IsSubColorIsomorphismPoset);
    SetFilterObj(poset,IsSubColorIsomorphismPosetRep);

    return poset;
end);

InstallMethod( ViewString,
        "for sub color isomorphism posets",
        [IsSubColorIsomorphismPoset],
function(poset)
    return Concatenation("<sub color isomorphism poset with ", String(Length(ElementsOfCocoPoset(poset))), " elements>");
end);
