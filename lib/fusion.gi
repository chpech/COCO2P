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
   return Objectify(NewType(FusionFamily(tensor), IsFusionOfTensor and IsFusionOfTensorRep), obj);
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

InstallMethod(OrderOfFusion,
        "for fusions of structure constants tensors",
        [IsFusionOfTensor],
function(fusion)
   return OrderOfCocoObject(TensorOfFusion(fusion));
end);

InstallOtherMethod(Order,
        "for fusions of structure constants tensors",
        [IsFusionOfTensor],
function(fusion)
   return OrderOfFusion(fusion);
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
        Error("SubOrbitsOfCocoOrbit: The given group is not a subgroup of the underlying group of the good set orbit!");
    fi;
    stab:=StabilizerOfCanonicalRepresentative(orb);
    cosreps:=List(DoubleCosetsNC(ug,stab, grp), Representative);
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
        Error("SubOrbitsWithInvariantPropertyOfCocoOrbit: The given group is not a subgroup of the underlying group of the good set orbit!");
    fi;

    stab:=StabilizerOfCanonicalRepresentative(orb);
    cosreps:=List(DoubleCosetsNC(ug,stab,grp), Representative); 
    rep:=CanonicalRepresentativeOfCocoOrbit(orb);
    nrep:=GoodSetOrbitNC(grp,rep, Intersection(stab,grp));
    cosreps:=Filtered(cosreps, r->func(OnFusions(CanonicalRepresentativeOfCocoOrbit(nrep),r)));
    res:=List(cosreps, x->OnCocoOrbits(nrep,x));
    return Set(res);
end);



#########################################################################################

InstallMethod(ViewString,
        "for fusions of tensors",
        [IsFusionOfTensor],
function(x)
    return Concatenation("<fusion of order ", String(OrderOfCocoObject(TensorOfFusion(x))), " and rank ", String(RankOfFusion(x)), ">");
end);

InstallMethod(ViewString,
        "for fusion orbits",
        [IsFusionOrbit],
        function(x)
    local res;
    
    res:="<";
    if IsMutable(x) then
        Append(res,"mutable ");
    fi;
    Append(res, Concatenation("FusionOrbit of length ", String(Size(x)),">"));
    return res;
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
        p1:=AsPartition(fs1);
        p2:=AsPartition(fs2);
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


InstallGlobalFunction(FusionOrbitsFromGoodSetOrbits,
function(gsorbits)
    local iter;

    
    iter:=IteratorOfPartialFusionOrbits(gsorbits);
    
    return AllFusionOrbits(iter);
    
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
    local fsorbs;

    if not ForAll(GeneratorsOfGroup(grp), g->IsAutomorphismOfObject(T,g)) then
        Error("The given group must preserve the tensor of structure-constants!");
        return fail;
    fi;
    
    fsorbs:=HomogeneousFusionOrbits(T);
    if Size(grp)< Size(AutomorphismGroup(T)) then
        fsorbs:=Union(List(fsorbs, fso->SubOrbitsOfCocoOrbit(grp,fso)));
    fi;
    
    return fsorbs;
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


DeclareRepresentation( "IsPosetOfFusionOrbitsRep",
        IsCocoPosetRep,
        ["elements",    
         "successors",
         "predecessors",
         "algTwins",
         "algebraicFusions",
         "colorGraphs",
         "cgr"
         ]);

InstallMethod(ComputationTime,
          "for posets of fusion orbits",
          [IsCocoPoset],
function(cgr)
    return "unknown";
end);


InstallGlobalFunction(PosetOfHomogeneousFusionOrbits,
function(cgr)
    local order, linorder, tensor, caut,aautfusorbs,cautfusorbs,ltwins,i,suborbs,twins,forb,part,isAlgFus,algebraicFusions,j,poset,mrg,runtime,tstart,rt;
    
    order:=function(yy,xx)
        local part1,part2,cosreps;
        
        part1:=AsPartition(Representative(cautfusorbs[yy]));
        part2:=AsPartition(Representative(cautfusorbs[xx]));
        
        if Length(part1)=Length(part2) then 
            return part1=part2;
        fi;
        
        cosreps:=List(DoubleCosetsNC(UnderlyingGroupOfCocoOrbit(cautfusorbs[xx]), StabilizerOfCanonicalRepresentative(cautfusorbs[xx]),  StabilizerOfCanonicalRepresentative(cautfusorbs[yy])),Representative);
        return ForAny(cosreps, r->ForAll(OnSetsSets(part2,r), x->ForAny(part1, y->IsSubset(y,x))));
    end;

    linorder:=function(x,y)
        return cautfusorbs[x]<cautfusorbs[y];
    end;

    
    runtime:=ValueOption("runtime");
    if runtime=fail then
        runtime:=false;
    fi;
    
    if runtime then
        tstart:=NanosecondsSinceEpoch();
    fi;
    
    
    tensor:=StructureConstantsOfColorGraph(cgr);
    caut:=ColorAutomorphismGroupOnColors(cgr);
    aautfusorbs:=Set(HomogeneousFusionOrbits(tensor));
    cautfusorbs:=[];ltwins:=[];
    algebraicFusions:=[];
    for i in [1..Length(aautfusorbs)] do
        suborbs:=SubOrbitsOfCocoOrbit(caut,aautfusorbs[i]);
        twins:=[Length(cautfusorbs)+1..Length(cautfusorbs)+Length(suborbs)];
        forb:=aautfusorbs[i];
        mrg:=AsPartition(CanonicalRepresentativeOfCocoOrbit(forb));
        part:=Orbits(Stabilizer(StabilizerOfCanonicalRepresentative(forb),mrg,OnTuplesSets),[1..Order(Representative(forb))]);
        if Length(part)=Length(mrg) then
            isAlgFus:=true;
        else
            isAlgFus:=false;
        fi;
        
        for j in [1..Length(suborbs)] do
            Add(cautfusorbs,suborbs[j]);
            Add(ltwins, Difference(twins, [twins[j]]));
            if isAlgFus then 
                Add(algebraicFusions,Length(cautfusorbs));
            fi;
        od;
        Info(InfoCOCO,1,"*");
    od;
    
    poset:=CocoPosetByFunctions([1..Length(cautfusorbs)], order, linorder);
    poset!.algTwins:=Immutable(List(poset!.elements, x->List(ltwins[x],y->Position(poset!.elements,y))));
    poset!.algebraicFusions:=Immutable(Filtered([1..Length(poset!.elements)], i->poset!.elements[i] in algebraicFusions));
    poset!.elements:=Immutable(List(poset!.elements, i->cautfusorbs[i]));
    poset!.colorGraphs:=Immutable(List(poset!.elements, forb->ColorGraphByFusion(cgr, CanonicalRepresentativeOfCocoOrbit(forb))));
    poset!.cgr:=cgr;
    
    
    SetFilterObj(poset,IsPosetOfFusionOrbits);
    SetFilterObj(poset,IsPosetOfFusionOrbitsRep);
    
    if runtime then
        rt:=StringTime(Int((NanosecondsSinceEpoch()-tstart)/1000000));
        RemoveCharacters(rt," ");
        
        SetComputationTime(poset, rt);
    fi;

    return poset;
end);

InstallMethod(InducedCocoPoset,
        "for posets of fusion orbits in PosetOfFusionOrbitsRep",
        [IsPosetOfFusionOrbits, IsPosetOfFusionOrbits and IsPosetOfFusionOrbitsRep,IsSet],
function(filter,forbposet,set)
    local npos;
    
    npos:=InducedCocoPoset(IsCocoPoset, forbposet,set);
    
    npos!.algTwins:=forbposet!.algTwins{set};
    npos!.algTwins:=List(npos!.algTwins, x->Intersection(x,set));
    npos!.algTwins:=List(npos!.algTwins, x->Position(set,x));
    MakeImmutable(npos!.algTwins);
        
    npos!.algebraicFusions:=Intersection(forbposet!.algebraicFusions,set);
    npos!.algebraicFusions:=List(npos!.algebraicFusions, x->Position(set,x));
    MakeImmutable(npos!.algerbaicFusions);
    
    npos!.colorGraphs:=forbposet!.colorGraphs{set};
    SetFilterObj(npos,IsPosetOfFusionOrbits);
    SetFilterObj(npos,IsPosetOfFusionOrbitsRep);
    
    npos!.cgr:=forbposet!.cgr;
    
    return npos;
end);
    
InstallOtherMethod(InducedCocoPoset,
        "for posets of fusion orbits in PosetOfFusionOrbitsRep",
        [IsPosetOfFusionOrbits and IsPosetOfFusionOrbitsRep,IsSet],
function(forbposet,set)
    return InducedCocoPoset(IsPosetOfFusionOrbits, forbposet,set);
end);

    
InstallMethod( ViewString,
        "for posets of fusion orbits",
        [IsPosetOfFusionOrbits],
function(poset)
    return Concatenation("<poset of fusion orbits with with ", String(Length(ElementsOfCocoPoset(poset))), " elements>");
end);

InstallOtherMethod(DisplayString,
                   "for posets of fusion orbits",
                   [IsPosetOfFusionOrbits and IsPosetOfFusionOrbitsRep, IsList],
function(pos, indices)
        local  idx,nodes, str, outp,res, cgr, node, v, ninf, maxlength,
           index, algtwins, strictupperbounds, maxin,nonsch,long,scgr,
           sch,mrg,schfiss,i,cgrr,fvc,srg,onlyfvc,cisomap,MapReps,map,
           cisorep,ord,filt,date,runtime,strucexp;
    
    
    MapReps:=function(i)
        local  list,fct, idx;
        
        list:=List(nodes, x->x!.cgr);
        fct:=IsColorIsomorphicColorGraph;
        
                 
        if not IsBound(pos!.cisoMap) then
            pos!.cisoMap:=[];
        fi;
        
        if IsBound(pos!.cisoMap[i]) then
            idx:=pos!.cisoMap[i];
        else
            idx:=First([1..Length(list)], j->fct(list[i],list[j]));
            pos!.cisoMap[i]:=idx;
        fi;
        
        if idx = i then
            Info(InfoCOCO,1,"+");
        else
            Info(InfoCOCO,1,"-");
        fi;
        return idx;
    end;
    
    
    filt:=ValueOption("filter");
    if filt=fail then
        filt:=ReturnTrue;
    fi;
    
    
    nonsch:=ValueOption("nonschurian");
    if nonsch=fail then
        nonsch:=false;
    fi;
    long:=ValueOption("long");
    if long=fail then
        long:=false;
    fi;

    schfiss:=ValueOption("schurianfission");
    if schfiss=fail then
        schfiss:=false;
    fi;
    
    fvc:=ValueOption("fvc");
    if fvc=fail then
        fvc:=false;
    fi;
    
    onlyfvc:=ValueOption("onlyfvc");
    if onlyfvc=fail then
        onlyfvc:=false;
    fi;
    
    cisomap:=ValueOption("cisomap");
    if cisomap=fail then
        cisomap:=false;
    fi;
    
    date:=ValueOption("date");
    if date=fail then
        date:=false;
    fi;
    
    runtime:=ValueOption("runtime");
    if runtime=fail then
        runtime:=false;
    fi;
    
    strucexp:=ValueOption("strucexp");
    if strucexp=fail then
        strucexp:=12;
    fi;
    
    
    for i in [1..Size(pos)] do
        cgrr:=pos!.colorGraphs[i];
        if Rank(cgrr)>2 and (Rank(cgrr)>3 or IsPrimitiveColorGraph(cgrr)) then
            ord:=PrimePowersInt(Size(AutomorphismGroup(cgrr)));
            ord:=ord{[2,4..Length(ord)]};
            if ForAll(ord, x->x<=strucexp) then
#            if RemInt(Size(AutomorphismGroup(cgrr)),2^12)<>0 then
                StructureDescription(AutomorphismGroup(cgrr):short);
            fi;
        fi;Info(InfoCOCO,1,".");
    od;
    Info(InfoCOCO,1,"|");
    
    nodes:=[];
    for i in [1..Size(pos)] do
        node:=NewCocoNode(pos!.colorGraphs[i]);
        node!.index:=i;
        node!.poset:=pos;
        RegisterInfoCocoNode(node, rec(name:="Number:", value:=String(node!.index)));
        RegisterStandardInfo@COCO2P(node);
        if fvc then
            if Rank(node!.cgr)=3 and IsSymmetricColorGraph(node!.cgr) and not IsSchurian(node!.cgr) then
                srg:=SrgFromCgr(node!.cgr);
                RegisterInfoCocoNode(node, rec(name:="4-vc:",
                                               value:=String(IsHighlyRegularGraph(srg,2,4))));
            fi;
        fi;
        
        RegisterInfoCocoNode(node, rec(name:="algebraic:", value:=String(node!.index in node!.poset!.algebraicFusions)));
        Add(nodes,node);
        Info(InfoCOCO,1,".");
    od;
    Info(InfoCOCO,1,"|");
    
    
    outp:="";
    res:=OutputTextString(outp,true);
    SetPrintFormattingStatus(res,false);


    PrintTo(res,"COCO2P - Information about a PosetOfFusionOrbits\n",
                "------------------------------------------------\n");
    cgr:=pos!.cgr;
    node:=NewCocoNode(cgr);
    RegisterStandardInfo@COCO2P(node);
    ninf:=node!.nodeInfo;

    ComputeAllInfos(node);
    for str in infoOptions@COCO2P.disabled do
        ComputeInfo(node,str);
    od;
    AppendTo(res, NodeInfoString(node));
    maxlength:=Maximum(ninf.maxlength, 20);
    if long and Rank(node!.cgr)>2 and not ( Rank(node!.cgr)=3 and not IsPrimitive(node!.cgr)) then
        if not IsTransitive(AutomorphismGroup(node!.cgr),[1..OrderOfColorGraph(cgr)]) then
            AppendTo(res, String("Orbits of Aut: ",-maxlength));
            AppendTo(res, StringCocoOrbReps@(AutomorphismGroup(node!.cgr),[1..OrderOfColorGraph(cgr)]));
        fi;
        AppendTo(res, String("Generators of Aut: ",-maxlength),"\n");
        AppendTo(res, StringCocoGenerators@(AutomorphismGroup(node!.cgr), OrderOfColorGraph(cgr)));
        
        scgr:=ColorGraph(AutomorphismGroup(node!.cgr),[1..OrderOfColorGraph(cgr)],OnPoints,true);
        if not IsSchurian(node!.cgr) then
            AppendTo(res, String("Merging in Cgr(Aut): ",-maxlength),"\n");
            mrg:=Set([1..Rank(node!.cgr)], i->Filtered([1..Rank(scgr)], j->ArcColorOfColorGraph(node!.cgr,ColorRepresentative(scgr,j))=i));
            AppendTo(res, StringCocoMerging@(mrg));
        fi;
    fi;
    AppendTo(res, "-------------------------------------------------\n");
    if date then
        PrintTo(res, String("                   Date: ",-maxlength), TodayString@(),"\n");
    fi;
    if runtime then
        PrintTo(res, String("                Runtime: ",-maxlength), ComputationTime(pos),"\n");
    fi;
    
    PrintTo(res, String("Number of fusion orbits: ",-maxlength), Length(nodes{indices}),"\n");
    PrintTo(res, String("              symmetric: ",-maxlength), Length(Filtered(nodes{indices}, x->IsSymmetricColorGraph(x!.cgr))),"\n");
    PrintTo(res, String("              primitive: ",-maxlength), Length(Filtered(nodes{indices}, x->IsPrimitiveColorGraph(x!.cgr))),"\n");
    PrintTo(res, String("  symmetric & primitive: ",-maxlength), Length(Filtered(nodes{indices}, x->IsSymmetricColorGraph(x!.cgr) and IsPrimitiveColorGraph(x!.cgr))),"\n");
    PrintTo(res, "-------------------------------------------------\n");
    
    
    
    idx:=0;
    
    for v in indices do
        node:=nodes[v];
        ninf:=node!.nodeInfo;
        if nonsch then
            if IsSchurian(node!.cgr) then
                continue;
            fi;
        fi;
        if onlyfvc then
            if Rank(node!.cgr)>3 or 
               not IsSymmetricColorGraph(node!.cgr) or 
                   IsSchurian(node!.cgr) or 
                   not IsHighlyRegularGraph(SrgFromCgr(node!.cgr),2,4) 
            then
                continue;
            fi;
        fi;
        if not filt(node!.cgr) then
            continue;
        fi;
        
        
        idx:=idx+1;

        maxlength:=Maximum(ninf.maxlength, 20);
        if nonsch or onlyfvc or filt<>ReturnTrue or indices <> [1..Size(pos)] then
            AppendTo(res,String("Index: ",-maxlength), idx,"\n");
        fi;
        index:=IndexOfCocoNode(node);
        
        
        AppendTo(res, NodeInfoString(node));
        algtwins:=Intersection(pos!.algTwins[index], indices);
        if not IsUndirectedColorGraph(node!.cgr) then
            AppendTo(res, String("asymm. mates: ",-maxlength), StringCocoPerm@(ColorMates(node!.cgr)));
        fi;
        if algtwins<>[] then
            AppendTo(res, String("Algebraic Twins: ",-maxlength), algtwins,"\n");
        fi;
        if schfiss then
            if not IsSchurian(node!.cgr) then
                if IsTransitive(AutomorphismGroup(node!.cgr),[1..OrderOfColorGraph(cgr)]) then
                    sch:=Filtered([1..Size(pos)], i->IsSchurian(pos!.colorGraphs[i]));
                    sch:=Intersection(FilterInCocoPoset(pos, v),sch);
                    sch:=MinimalElementsInCocoPoset(pos,sch);
                    Assert(1,Length(sch)=1);
                    Assert(1,sch[1]<>v);
                    AppendTo(res, String("Schurian fission: ",-maxlength), sch[1],"\n");
                fi;
            fi;
        fi;


        strictupperbounds:=Difference(FilterInCocoPoset(pos,index),[index]);
        strictupperbounds:=Intersection(strictupperbounds,indices);
        maxin:=[];
        if strictupperbounds<>[] then
            maxin:=MinimalElementsInCocoPoset(pos,strictupperbounds);
        fi;

        AppendTo(res, String("Maximal Merging in: ",-maxlength), maxin,"\n");
        if cisomap then
            cisorep:=MapReps(index);
            if cisorep<>index then
                AppendTo(res, String("C-isomorphic to: ",-maxlength), "#",cisorep,"\n");
            fi;
        fi;
        if long and Rank(node!.cgr)>2 and not (Rank(node!.cgr)=3 and not IsPrimitive(node!.cgr)) then
            if not IsTransitive(AutomorphismGroup(node!.cgr),[1..OrderOfColorGraph(cgr)]) then
                AppendTo(res, String("Orbits of Aut: ",-maxlength));
                AppendTo(res, StringCocoOrbReps@(AutomorphismGroup(node!.cgr),[1..OrderOfColorGraph(cgr)]));
            fi;
            AppendTo(res, String("Generators of Aut: ",-maxlength),"\n");
            AppendTo(res, StringCocoGenerators@(AutomorphismGroup(node!.cgr), OrderOfColorGraph(cgr)));

            scgr:=ColorGraph(AutomorphismGroup(node!.cgr),[1..OrderOfColorGraph(cgr)],OnPoints,true);
            if not IsSchurian(node!.cgr) then
                AppendTo(res, String("Merging in Cgr(Aut): ",-maxlength),"\n");
                mrg:=Set([1..Rank(node!.cgr)], i->Filtered([1..Rank(scgr)], j->ArcColorOfColorGraph(node!.cgr,ColorRepresentative(scgr,j))=i));
                AppendTo(res, StringCocoMerging@(mrg));
            fi;
        fi;

        AppendTo(res,"\n");
    od;

    CloseStream(res);
    return outp;
end);


InstallMethod(ConstructorOfCocoOrbit,
        "for all fusion orbits",
        [IsFusionOrbit],
function(orb)
    return FusionOrbit;
end);

InstallMethod(ConstructorOfCocoOrbitNC,
        "for all fusion orbits",
        [IsFusionOrbit],
function(orb)
    return FusionOrbitNC;
end);

InstallMethod(DisplayString,
                   "for posets of fusion orbits",
                   [IsPosetOfFusionOrbits and IsPosetOfFusionOrbitsRep],
function(pos)
    return DisplayString(pos,[1..Size(pos)]);
end);


