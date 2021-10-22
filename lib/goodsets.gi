#############################################################################
##
##  goodsets.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of good sets
##
#############################################################################

RowDegreeList:=function(T,M)
    local i,res,sb;
    res:=List([1..NumberOfFibres(T)], x->0);
    for i in M do
       sb:=StartBlock(T,i);
       res[sb]:=res[sb]+OutValencies(T)[i];
    od;
    return res;
end;

ColDegreeList:=function(T,M)
    local i,res,fb;
    res:=List([1..NumberOfFibres(T)], x->0);
    for i in M do
       fb:=FinishBlock(T,i);
       res[fb]:=res[fb]+OutValencies(T)[i^Mates(T)];
    od;
    return res;
end;

BlockingMat:=function(T,M)
    local nof,sb,fb,res,i;
    
    nof:=NumberOfFibres(T);
    res:=List([1..nof], i->List([1..nof], j->[]));
    for i in M do
        sb:=StartBlock(T,i);
        fb:=FinishBlock(T,i);
        AddSet(res[sb][fb],i);
    od;
    return res;
end;


####################################################################################

DeclareRepresentation("IsGoodSetRep",
        IsAttributeStoringRep,
        [ "tensor",             # the tensor over which the good set "lives"
          "set",                # the good set of colors of <tensor>
          "part",               # the WL-stable partition induced by <set>
        ]);

InstallGlobalFunction(BuildGoodSet,
function(arg)
   local tensor,set,part,res;

   tensor:=arg[1];
   set:=arg[2];
   if Length(arg)=3 then
       part:=arg[3];
   else
       part:=WLBuildSymGoodSetPartition(tensor,set);
       part:=WLStabil(tensor,part);
       if part=fail then
           return fail;
       fi;
       part:=part.classes;
   fi;


   res:=rec(
            tensor:=tensor,
            set:=Immutable(set),
            part:=Immutable(part));
   return Objectify(NewType(GoodSetsFamily(tensor), IsGoodSet and IsGoodSetRep), res);
end);

InstallMethod(TensorOfGoodSet,
        "for good sets in GoodSetRep",
        [IsGoodSet and IsGoodSetRep],
function(gs)
   return gs!.tensor;
end);

InstallOtherMethod(AsSet,
        "for good sets in GoodSetRep",
        [IsGoodSet and IsGoodSetRep],
function(gs)
  return gs!.set;
end);

InstallOtherMethod(Length,
        "for good sets",
        [IsGoodSet],
function(gs)
    return Length(AsSet(gs));
end);

InstallOtherMethod(\<,
        "for good sets",
        IsIdenticalObj,
        [IsGoodSet,IsGoodSet],
function(gs1,gs2)
    if Length(gs1)<>Length(gs2) then
        return Length(gs1)<Length(gs2);
    else
        return AsSet(gs1)<AsSet(gs2);
    fi;
end);

InstallOtherMethod(\=,
        "for good sets",
        IsIdenticalObj,
        [IsGoodSet,IsGoodSet],
function(gs1,gs2)
    return AsSet(gs1)=AsSet(gs2);
end);


# <g> must be from Aut(<gs!.tensor>)
InstallMethod(OnGoodSets,
        "for good sets in GoodSetRep",
        [IsGoodSet and IsGoodSetRep, IsPerm],
function(gs, g)
    local res;
   res:=rec(
            tensor:=gs!.tensor,
            set:=MakeImmutable(OnSets(gs!.set,g)),
            part:=MakeImmutable(OnSetsSets(gs!.part,g)));
   return Objectify(NewType(GoodSetsFamily(gs!.tensor), IsGoodSet and IsGoodSetRep), res);
end);

InstallMethod(PartitionOfGoodSet,
        "for good sets in GoodSetRep",
        [IsGoodSet and IsGoodSetRep],
function(gs)
    return gs!.part;
end);

InstallOtherMethod(Size,
        "for good sets in GoodSetRep",
        [IsGoodSet and IsGoodSetRep],
function(gs)
    return Size(gs!.set);
end);

InstallMethod(ViewString,
        "for good set orbits",
        [IsGoodSet and IsGoodSetRep],
        function(x) local s,t,res;
    
    t:=TensorOfGoodSet(x);
    s:=AsSet(x);

    res:="<";
    if s<>[] and not s[1]^Mates(t) in s then
        Append(res,"antisymmetric ");
    else
        Append(res, "symmetric ");
    fi;

    return Concatenation(res, "GoodSet ", String(s), ">");
end);

InstallGlobalFunction(GoodSetOrbit,
function(arg)
    local group,gs,stab, can,xstab,nstab;

    group:=arg[1];
    gs:=arg[2];
    if Length(arg)=2 then
        stab:=Stabilizer(group,AsSet(gs), OnSets);
    else
        stab:=arg[3];
    fi;

    can:=SetCanonifiers(Stbc(group), Stbc(stab), AsSet(gs));
    nstab:=ClosureGroup(stab, List(can, x->can[1]*x^(-1)));


    return GoodSetOrbitNC(group, OnGoodSets(gs,can[1]), nstab^can[1]);
end);

InstallGlobalFunction(GoodSetOrbitNC,
function(arg)
    local group,gs,stab,res;

    group:=arg[1];
    gs:=arg[2];
    if Length(arg)=2 then
        stab:=Stabilizer(group,AsSet(gs), OnSets);
    else
        stab:=arg[3];
    fi;

    res:=rec(
            group:=group,
            rep:=gs,
            stab:=stab);
   return Objectify(NewType(GoodSetOrbitFamily(TensorOfGoodSet(gs),group), IsGoodSetOrbit and IsCocoOrbitRep), res);
end);

InstallMethod(OnCocoOrbits,
        "for all good set orbits",
        [IsGoodSetOrbit, IsPerm],
function(gsorb,perm)
    local   grp,  gs,  stab,  ngs,  ngrp,  nstab;

    grp:=UnderlyingGroupOfCocoOrbit(gsorb);
    gs:=CanonicalRepresentativeOfCocoOrbit(gsorb);
    stab:=StabilizerOfCanonicalRepresentative(gsorb);

    ngs:=OnGoodSets(gs,perm);
    return GoodSetOrbit(grp,ngs,Stabilizer(grp,AsSet(ngs),OnTuples),FamilyObj(gsorb));
end);



InstallMethod(SubOrbitsOfCocoOrbit,
        "for all set orbits",
        [IsPermGroup, IsGoodSetOrbit],
function(grp,gsorb)
    local   ug,  cosreps,  stab,  gs,  ngs;


    ug:=UnderlyingGroupOfCocoOrbit(gsorb);

    if not IsSubgroup(ug,grp) then
        Error("SubOrbitsOfCocoOrbit: The given group is not a subgroup of the underlying group of the orbit!");
    fi;
    stab:=StabilizerOfCanonicalRepresentative(gsorb);
    cosreps:=List(DoubleCosetsNC(ug,stab,grp), Representative); 
    gs:=CanonicalRepresentativeOfCocoOrbit(gsorb);
    ngs:=GoodSetOrbitNC(grp,gs, Intersection(stab,grp));

    return List(cosreps, x->OnCocoOrbits(ngs,x));
end);

InstallMethod(SubOrbitsWithInvariantPropertyOfCocoOrbit,
        "for good set orbits",
        [IsPermGroup, IsGoodSetOrbit, IsFunction],
function(grp,gsorb,func)
    local   ug,  cosreps,  stab,  gs,  ngs,  res;

    ug:=UnderlyingGroupOfCocoOrbit(gsorb);

    if not IsSubgroup(ug,grp) then
        Error("SubOrbitsWithInvariantPropertyOfCocoOrbit: The given group is not a subgroup of the underlying group of the orbit!");
    fi;

    stab:=StabilizerOfCanonicalRepresentative(gsorb);
    cosreps:=List(DoubleCosetsNC(ug,stab,grp), Representative); 
    gs:=CanonicalRepresentativeOfCocoOrbit(gsorb);
    ngs:=GoodSetOrbitNC(grp,gs, Intersection(stab,grp));
    res:=List(cosreps, x->OnCocoOrbits(ngs,x));
    res:=Filtered(res, x->func(CanonicalRepresentativeOfCocoOrbit(x)));

    return Set(res);
end);



# InstallMethod(CocoOrbitFamily,
#         "for good set orbits",
#         [IsGoodSetOrbit],
# function(gso)
#     return NewFamily("GoodSetOrbitFam", IsGoodSetOrbit);
# end);


InstallMethod(HomogeneousSymGoodSetOrbits,
        "for structure constants tensors",
        [IsTensor and IsTensorOfCC],
function(tensor)
    return Filtered(AllGoodSetOrbits(IteratorOfPartialGoodSetOrbits(AutomorphismGroup(tensor), EmptySymPartialGoodSet(tensor))),orb->AsSet(Representative(orb))<>[]);
end);

InstallMethod(HomogeneousAsymGoodSetOrbits,
        "for structure constants tensors",
        [IsTensor and IsTensorOfCC],
function(tensor)
    local agsorbs,aaut;
    
    aaut:=AutomorphismGroup(tensor);
    aaut:=ClosureGroup(aaut,[Mates(tensor)]);
    
    agsorbs:=AllGoodSetOrbits(IteratorOfPartialGoodSetOrbits(aaut,EmptyAsymPartialGoodSet(tensor)));
    agsorbs:=Filtered(agsorbs, orb->AsSet(Representative(orb))<>[]);
    
    return Union(List(agsorbs, orb->SubOrbitsOfCocoOrbit(AutomorphismGroup(tensor),orb)));    
end);

InstallMethod(HomogeneousGoodSetOrbits,
        "for structure constants tensors",
        [IsTensor and IsTensorOfCC],
function(tensor)
    local lgs,sym,prim;
    
    sym:=ValueOption("sym");
    if sym=fail then
        sym:=false;
    fi;
    prim:=ValueOption("prim");
    if prim=fail then
        prim:=false;
    fi;
    lgs:=Set(HomogeneousSymGoodSetOrbits(tensor));
    if not sym then
        lgs:=Union(lgs, HomogeneousAsymGoodSetOrbits(tensor));
    fi;
    if prim then
        lgs:=Filtered(lgs, x->ClosureSet(tensor, AsSet(Representative(x)))=[1..OrderOfTensor(tensor)]);
    fi;
    
    return lgs;
end);

InstallOtherMethod(HomogeneousGoodSetOrbits,
        "for structure constants tensors",
        [IsTensor and IsTensorOfCC, IsString],
function(tensor,mode)
    local   lgsorb;

    lgsorb:=[];

    if 'a' in mode then
        lgsorb:=HomogeneousAsymGoodSetOrbits(tensor);
    fi;
    if 's' in mode then
        lgsorb:=Union(lgsorb,HomogeneousSymGoodSetOrbits(tensor));
    fi;

    return lgsorb;
end);

InstallMethod(ActionOfCocoOrbit,
        "for all fusion orbits",
        [IsGoodSetOrbit],
function(orb)
    return OnGoodSets;
end);

InstallMethod(ViewString,
        "for good set orbits",
        [IsGoodSetOrbit],
        function(x)
    local res;
    
    res:=("<");
    if IsMutable(x) then
        Append(res, "mutable ");
    fi;
    return Concatenation(res, "GoodSetOrbit of length ", String(Size(x)), ">");
end);
