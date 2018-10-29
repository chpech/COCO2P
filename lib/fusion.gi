#############################################################################
##
##  fusion.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of the fusion-datatype
##
#############################################################################

DeclareRepresentation("IsFusionOfTensorRep",
        IsAttributeStoringRep,
        ["tensor",          # the structure constants tensor over which the fusion lives
         "partition"        # the partition of colors of tensor defining the fusion
]);

InstallGlobalFunction(FusionFromPartition,
function(arg)
   local tensor,set,part,res;

   tensor:=arg[1];
   part:=arg[2];
   if not WLIsStablePartition(tensor,part) then
       return fail;
   fi;
   return FusionFromPartitionNC(tensor,part);
end);


InstallGlobalFunction(FusionFromPartitionNC,
function(tensor,part)
   local obj;

   obj:=rec(
   			   tensor := tensor,
   			partition := Immutable(ShortLexSorted(part)));
   return Objectify(NewType(FusionFamily(tensor), IsFusionOfTensorRep), obj);
end);

InstallGlobalFunction(FusionFromPartitionAndBaseNC,
function(tensor,part,bas)
   local obj;

   obj:=rec(
   			   tensor := tensor,
   			partition := Immutable(ShortLexSorted(part)));
   obj:=Objectify(NewType(FusionFamily(tensor), IsFusionOfTensorRep), obj);
   SetBaseOfFusion(obj,SSortedList(bas));
   return obj;
end);

InstallMethod(AsPartition,
        "for fusions in FusionOfTensorRep",
        [IsFusionOfTensor and IsFusionOfTensorRep],
function(f)
    local res;
    res:=Set(f!.partition, ShallowCopy);
    MakeImmutable(res);
    return res;
end);

InstallMethod(TensorOfFusion,
        "for fusions in FusionOfTensorRep",
        [IsFusionOfTensor and IsFusionOfTensorRep],
function(f)
   return f!.tensor;
end);


InstallMethod(RankOfFusion,
		"for fusions of structure constants tensors",
		[IsFusionOfTensor and IsFusionOfTensorRep],
function(fusion)
   return Length(fusion!.partition);
end);

InstallOtherMethod(Rank,
		"for fusions of structure constants tensors",
		[IsFusionOfTensor],
function(fusion)
   return RankOfFusion(fusion);
end);

InstallMethod(PartitionOfFusion,
        "for fusions of structure constants tensors",
        [IsFusionOfTensor and IsFusionOfTensorRep],
function(fusion)
    return fusion!.partition;
end);


InstallMethod(SubOrbitsOfCocoOrbit,
        "for all fusion orbits",
        [IsPermGroup, IsFusionOrbit],
function(grp,orb)
    local   ug,  cosreps,  stab,  rep,  nrep;


    ug:=UnderlyingGroupOfCocoOrbit(orb);

    if not IsSubgroup(ug,grp) then
        Error("SubOrbitsOfGoodSetOrbit: The given group is not a subgroup of the underlying group of the good set orbit!");
    fi;
    cosreps:=List(RightCosetsNC(ug,grp), x->Representative(x)^(-1)); # get left-coset representatives
    stab:=StabilizerOfCanonicalRepresentative(orb);
    rep:=CanonicalRepresentativeOfCocoOrbit(orb);
    nrep:=FusionOrbitNC(grp,rep, Intersection(stab,grp));

    return Set(cosreps, x->OnCocoOrbits(nrep,x));
end);

InstallMethod(SubOrbitsWithInvariantPropertyOfCocoOrbit,
        "for fusion orbits",
        [IsPermGroup, IsFusionOrbit, IsFunction],
function(grp,orb,func)
    local   ug,  cosreps,  stab,  rep,  nrep,  res;

    ug:=UnderlyingGroupOfCocoOrbit(orb);

    if not IsSubgroup(ug,grp) then
        Error("SubOrbitsOfGoodSetOrbit: The given group is not a subgroup of the underlying group of the good set orbit!");
    fi;

    cosreps:=List(RightCosetsNC(ug,grp), x->Representative(x)^(-1)); # get left-coset representatives
    stab:=StabilizerOfCanonicalRepresentative(orb);
    rep:=CanonicalRepresentativeOfCocoOrbit(orb);
    nrep:=GoodSetOrbitNC(grp,rep, Intersection(stab,grp));
    cosreps:=Filtered(cosreps, r->func(OnFusions(CanonicalRepresentativeOfCocoOrbit(nrep),r)));
    res:=List(cosreps, x->OnCocoOrbits(nrep,x));
    return Set(res);
end);



#########################################################################################

InstallMethod(ViewObj,
        "for fusions of tensors",
        [IsFusionOfTensor],
function(x)
    Print("<");
    Print("fusion of order ", OrderOfCocoObject(TensorOfFusion(x)),
          " and rank ", RankOfFusion(x), ">");
end);

InstallMethod(ViewObj,
        "for fusion orbits",
        [IsFusionOrbit],
        function(x)
    Print("<");
    if IsMutable(x) then
        Print("mutable ");
    fi;
    Print("FusionOrbit of length ", Size(x),">");
end);



InstallOtherMethod(\<,
        "for fusions of tensors",
        IsIdenticalObj,
        [IsFusionOfTensor,IsFusionOfTensor],
function(fs1,fs2)
    local   p1,  p2,  i;
    if RankOfFusion(fs1)<>RankOfFusion(fs2) then
        return RankOfFusion(fs1)<RankOfFusion(fs2);
    else
        p1:=PartitionOfFusion(fs1);
        p2:=PartitionOfFusion(fs2);
        for i in [1..Length(p1)] do
            if Length(p1[i])<>Length(p2[i]) then
                return Length(p1[i])<Length(p2[i]);
            elif p1[i]<>p2[i] then
                return p1[i]<p2[i];
            fi;
        od;
    fi;
    return false;
end);

InstallOtherMethod(\=,
        "for fusions of tensors",
        IsIdenticalObj,
        [IsFusionOfTensor,IsFusionOfTensor],
function(fs1,fs2)
    return PartitionOfFusion(fs1)=PartitionOfFusion(fs2);
end);


InstallGlobalFunction(WLRefinedPartition,
function(newPart,gs)
    local   repart,  T,  M,  res,  iM,xres;
    repart:=function(newPart,u,fix)
        local   i,  newclass;
        i:=1;
        while i<=Length(newPart.variable) and
          not IsSubset(WLPartitionClass(newPart,newPart.variable[i]),u) do
            i:=i+1;
        od;
        if i > Length(newPart.variable) then
            return fail;
        fi;

        i:=newPart.variable[i];
        if WLPartitionClass(newPart,i)=u then
            if fix then
                RemoveSet(newPart.variable,i);
                AddSet(newPart.fixed,i);
            fi;
            WLInstabilQueueAdd(newPart,i);

            return newPart;
        fi;
        newclass:=Difference(WLPartitionClass(newPart,i), u);
        if Length(newclass)<Length(u)  then
            return fail;
        fi;
        if fix and Length(newclass)=Length(u) and newclass<u then
            return fail;
        fi;

        newPart.classes[i]:=newclass;
        WLInstabilQueueAdd(newPart,i);
        Add(newPart.classes,u);
        if fix then
            AddSet(newPart.fixed, Length(newPart.classes));
        else
            AddSet(newPart.variable,Length(newPart.classes));
        fi;


        newPart.instabilFlags[Length(newPart.classes)]:=false;
        newPart.totestFlags[Length(newPart.classes)]:=false;
        WLInstabilQueueAdd(newPart, Length(newPart.classes));
        return newPart;
    end;

    T:=TensorOfGoodSet(gs);
    M:=AsSet(gs);
    iM:=OnSets(M,Mates(T));

    res:=repart(newPart,M,true);
    if res=fail then
        return fail;
    fi;


    if iM>M then
        res:=repart(res,iM,false);
        if res=fail then
            return fail;
        fi;
    fi;

    return res;
end);




InstallGlobalFunction(ShortLexSorted,
function(part)
    local spart;

    spart:=ShallowCopy(part);
    Sort(spart, function(a,b)
        if Length(a)=Length(b) then
            return a<b;
        else
            return Length(a)<Length(b);
        fi;
    end);
    return spart;
end);

# A good set is compatible with a stable partition if
# 0 if it is lexicographical larger than its mate, then its mate has to be fixed
# 1 It does not split a fixed class
# 2 When splitting a variable class, then the new classes have cardinality >= m (the maximum cardinality of a fixed set)
# 3 the good set should be contained in a variable class
InstallGlobalFunction(IsCompatibleGS,
function(part,gs)
    local   gspart,  igspart,  m,  M,  T,  iM,  i,  j,  cls,  c,  len;
    gspart:=PartitionOfGoodSet(gs);

    igspart:=[];
    m :=Maximum(List(part.fixed, i->Length(part.classes[i])));

    M:=AsSet(gs);
    T:=TensorOfGoodSet(gs);
    iM:=OnSets(M,Mates(T));
    if iM<M then
        if not ForAny(part.fixed, i->part.classes[i]=iM) then
#            Print("A\c");
            return false;
        fi;
    fi;

    for i in [1..Length(gspart)] do
        for j in gspart[i] do
            igspart[j]:=i;
        od;
    od;

    for i in part.fixed do
        j:=igspart[part.classes[i][1]];
        if not IsSubset(gspart[j],part.classes[i]) then
#            Print("B\c");
            return false;
        fi;
    od;

    for i in part.variable do
        cls:=part.classes[i];
        if cls[1] in ReflexiveColors(TensorOfGoodSet(gs)) then
            continue;
        fi;
        if Intersection(cls,AsSet(gs))<>[] and not IsSubset(cls, AsSet(gs)) then
#            Print("C\c");
            return false;
        fi;
    od;

    for i in part.variable do
        cls:=part.classes[i];
        if cls[1] in ReflexiveColors(TensorOfGoodSet(gs)) then
            continue;
        fi;

        for c in gspart do
            if c[1] in  ReflexiveColors(TensorOfGoodSet(gs)) or c=AsSet(gs) then
                continue;
            fi;

            len:=Length(Intersection(c,cls));
            if len=0 then
                continue;
            fi;
            if len<m then
#                Print("D\c");
                return false;
            fi;
        od;
    od;
    return true;
end);



InstallGlobalFunction(FusionOrbitsFromGoodSetOrbits,
function(gsorbits)
    local recure,pparts,AddToPParts,drawers,counter,g,domain,T;


    AddToPParts:=function(stabppart, ppart,part)
        local drawer,i,pos,newd,ngp,spart,gens;

        counter:=counter+1;

        spart:=ShortLexSorted(part.classes);
#        if counter mod 1 = 0 then
        COCOPrint("*\c");
#        fi;

        if not IsBound(pparts[Length(spart)]) then
            pparts[Length(spart)]:=[];
        fi;

        drawer:=pparts[Length(spart)];
        newd:=false;
        for i in [1..Length(spart)] do
            pos:=Length(spart[i]);
            if not IsBound(drawer[pos]) then
                drawer[pos]:=[];newd:=true;
            fi;
            drawer:=drawer[pos];
        od;
        if newd then
            Add(drawers,drawer);
        fi;
        gens:=SetsSetsCanonifiers(g,stabppart,spart);
        spart:=FusionFromPartitionAndBaseNC(T,spart,ShallowCopy(ppart));
        spart:=FusionOrbitNC(g,spart,ClosureGroup(stabppart,gens));

#        if spart in drawer then
#            return false;
#        else
            Add(drawer,spart);
#        fi;
#        return true;
    end;


    recure:=function(gg,gp,ppart,dom,slice,gsorbs,part,base)
        local   lastM,  minlength,  spart,  minvar,  gsorb,  gs,  m,
                newpart,  mgp,  ngp,  newslice,  ngg,  newppart,
                newbase,  lm,  newdom,  min,  max,  ngsorbs,f;


        if ppart<>[] then
            lastM:=ppart[Length(ppart)];
            minlength:=Length(lastM);
        else
            lastM:=[1];
            minlength:=1;
        fi;

        spart:=ShortLexSorted(Filtered(part.classes{part.variable},x->not x[1] in ReflexiveColors(T)));
        if spart=[] or gsorbs=[]  or not spart[1] in Set(gsorbs, x->AsSet(CanonicalRepresentativeOfCocoOrbit(x))) then
            AddToPParts(gp,base,part);
        fi;


        if spart=[] then
            return;
        fi;

        minvar:=Minimum(List(spart,Length));
#        Print(ppart,"\n",spart,"\n",List(gsorbs, x->AsSet(Representative(x))),"\n\n");

        for gsorb in gsorbs do
            gs:=CanonicalRepresentativeOfCocoOrbit(gsorb);
            m:=AsSet(gs);


            if Length(m)>minvar then
#                Print("0\c");
                break;
            fi;
            if Length(m)=minvar and m > spart[1] then
#                Print("^\c");
                break;
            fi;


            newpart:=WLShallowCopyStablePartition(part);
            newpart:=WLRefinedPartition(newpart,gs);


            if newpart=fail then
#                Print("1\c");
                continue;
            fi;

            if slice<>[] and Length(m)=Length(slice[1]) then
                if  m < slice[Length(slice)] then
#                    Print("2\c");
                    continue;
                fi;

                mgp:=StabilizerOfCanonicalRepresentative(gsorb);

                ngp:=SetsSetsReducibilityTestOneCard(gg, mgp,slice,m);

                if IsPerm(ngp) then
#                    Print("3\c");
                    continue;
                fi;
                newslice:=Concatenation(slice,[m]);
                ngg:=gg;
            else
                ngp:=Intersection(gp, StabilizerOfCanonicalRepresentative(gsorb));
                mgp:=ngp;

                ngg:=gp;
                newslice:=[m];
            fi;
            newppart:=Concatenation(ppart,[m]);
            newbase:=ShallowCopy(base);


            if Length(newpart.classes)>Length(part.classes) then
                newpart:=WLStabil(TensorOfGoodSet(gs), newpart,m);

                if newpart=fail then
#                    Print("4\c");
                    continue;
                fi;

                lm:=Filtered(newpart.variable, x->Length(newpart.classes[x])=Length(m));
                lm:=newpart.classes{lm};
                if ForAny(lm, x->(not x[1] in ReflexiveColors(TensorOfGoodSet(gs))) and x<m) then
#                    Print("5\c");

                    continue;
                fi;
                Add(newbase,m);
            fi;

            newdom:=Difference(dom,m);
            min:=Length(m);
            max:=Maximum(List(newpart.classes{newpart.variable},Length));

            ngsorbs:=RefineFuseAndFilterGoodSetOrbits(mgp,ngp,Filtered(gsorbs, x->min<=Length(CanonicalRepresentativeOfCocoOrbit(x)) and Length(CanonicalRepresentativeOfCocoOrbit(x))<=max),newpart,newdom);

            recure(ngg,ngp,newppart,newdom,newslice,ngsorbs,newpart,newbase);
        od;

    end;
    counter:=0;

    drawers:=[];
    pparts:=[];
    if gsorbits=[] then
        return [];
    fi;

    g:=UnderlyingGroupOfCocoOrbit(gsorbits[1]);
    T:=TensorOfGoodSet(CanonicalRepresentativeOfCocoOrbit(gsorbits[1]));
    domain:=[1..Order(T)];

    recure(g,g, [],domain,[],gsorbits,WLBuildTrivialPartition(T),[]);
    return drawers;
end);

InstallGlobalFunction(RefineFuseAndFilterGoodSetOrbits,
function(smallgrp,largegrp,gsorbs,xpart,dom)
    local    res,  gso,  xgso,f;


    if gsorbs=[] then
        return [];
    fi;

    res:=[];
    f:=largegrp=smallgrp;


    for gso in gsorbs do

        xgso:=SubOrbitsWithInvariantPropertyOfCocoOrbit(smallgrp,gso,x->IsSubset(dom,AsSet(x)) and IsCompatibleGS(xpart,x));
        if not f  then
            UniteSet(res,Set(xgso, gso->GoodSetOrbit(largegrp, CanonicalRepresentativeOfCocoOrbit(gso),
                    ClosureGroup(StabilizerOfCanonicalRepresentative(gso), Stabilizer(largegrp, AsSet(CanonicalRepresentativeOfCocoOrbit(gso)),OnTuples)))));
        else
            UniteSet(res,xgso);
        fi;
    od;

    return res;
end);

# FusionOrbit(<group>, <fusion> [,<stab>] )
# <stab> is supposed to be a subgroup of the stabilizer of <fusion> in <group>
InstallGlobalFunction(FusionOrbit,
function(arg)
    local group,fusion,stab, can,xstab,nstab;

    group:=arg[1];
    fusion:=arg[2];
    if Length(arg)=2 then
        stab:=Stabilizer(group,AsPartition(fusion), OnSetsSets);
    else
        stab:=arg[3];
    fi;

    can:=SetsSetsCanonifiers(group, stab, PartitionOfFusion(fusion));
    nstab:=ClosureGroup(stab, List(can, x->can[1]*x^(-1)));


    return FusionOrbitNC(group, OnFusions(fusion,can[1]), nstab^can[1]);
end);

# <g> must be from Aut(<fusion!.tensor>)
InstallMethod(OnFusions,
        "for fusions in FusionOfTensorRep",
        [IsFusionOfTensor and IsFusionOfTensorRep, IsPerm],
function(fusion, g)
    local res;
    res:=rec(
             tensor:=fusion!.tensor,
             partition:=MakeImmutable(ShortLexSorted(OnSetsSets(Set(fusion!.partition),g)))
    );

    return Objectify(NewType(FusionFamily(fusion!.tensor), IsFusionOfTensor and IsFusionOfTensorRep), res);
end);


# FusionOrbitNC(<group>, <fusion> [,<stab>])
# <fusion> is a fusion that is assumed to be minimal (rev-lex wise) in its orbit
# the minimality property is not checked
# <stab> is supposed to be the full (SetsSets-wise) stabilizer of <fusion> in <group>
InstallGlobalFunction(FusionOrbitNC,
function(arg)
    local group,fusion,stab,res;

    group:=arg[1];
    fusion:=arg[2];
    if Length(arg)=2 then
        stab:=Stabilizer(group,AsPartition(fusion), OnSetsSets);
    else
        stab:=arg[3];
    fi;

    res:=rec(
            group:=group,
            rep:=fusion,
            stab:=stab);
   return Objectify(NewType(FusionOrbitFamily(TensorOfFusion(fusion),group), IsFusionOrbit and IsCocoOrbitRep), res);
end);

InstallMethod(HomogeneousFusionOrbits,
        "for structure constant tensors",
        [IsTensor and IsTensorOfCC],
function(tensor)
    local gsorbs;

    gsorbs:=HomogeneousGoodSetOrbits(tensor);
    return FusionOrbitsFromGoodSetOrbits(gsorbs);
end);

InstallOtherMethod(HomogeneousFusionOrbits,
        "for structure constant tensors",
        [IsPermGroup, IsTensor and IsTensorOfCC],
function(grp,T)
    local gsorbs;

    if not ForAll(GeneratorsOfGroup(grp), g->IsAutomorphismOfObject(T,g)) then
        Error("The given group must preserve the tensor of structure-constants!");
        return fail;
    fi;

    gsorbs:=HomogeneousGoodSetOrbits(grp,T);
    return FusionOrbitsFromGoodSetOrbits(gsorbs);
end);

InstallMethod(OnCocoOrbits,
        "for all fusion orbits",
        [IsFusionOrbit, IsPerm],
function(orb,perm)
    local   grp,  rep,  stab,  nrep;

    grp:=UnderlyingGroupOfCocoOrbit(orb);
    rep:=CanonicalRepresentativeOfCocoOrbit(orb);
    stab:=StabilizerOfCanonicalRepresentative(orb);

    nrep:=OnFusions(rep,perm);
    return FusionOrbit(grp,nrep,Stabilizer(grp,AsPartition(nrep),OnSetsSets));
end);

InstallMethod(ActionOfCocoOrbit,
        "for all fusion orbits",
        [IsFusionOrbit],
function(orb)
    return OnFusions;
end);
