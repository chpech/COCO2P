DeclareRepresentation("IsCocoOrbitRep",
                      IsAttributeStoringRep,
                      [ "group",            # the group over which the orbit is taken
                        "rep",              # a canonical representative of the orbit
                        "stab"              # the stabilizer of rep in <group>
                      ] );


InstallMethod(CanonicalRepresentativeOfCocoOrbit,
        "for all coco orbits in CocoOrbitRep",
        [IsCocoOrbit and IsCocoOrbitRep],
function(orb)
    return orb!.rep;
end);

InstallMethod(UnderlyingGroupOfCocoOrbit,
        "for all coco orbits in CocoOrbitRep",
        [IsCocoOrbit and IsCocoOrbitRep],
function(orb)
    return orb!.group;
end);

InstallMethod(StabilizerOfCanonicalRepresentative,
        "for all coco orbits in CocoOrbitRep",
        [IsCocoOrbit and IsCocoOrbitRep],
function(orb)
    return orb!.stab;
end);




InstallMethod(SubOrbitsWithInvariantPropertyOfCocoOrbit,
        "for all coco orbits",
        [IsPermGroup, IsCocoOrbit, IsFunction],
function(grp,gsorb,func)
    local  ug, stab, gs, res, cosreps, i, signs, cr, ngs;

    ug:=UnderlyingGroupOfCocoOrbit(gsorb);
    
    if ug=grp and func(Representative(gsorb)) then
        return [gsorb];
    fi;
    
    if not IsSubgroup(ug,grp) then
        Error("SubOrbitsWithInvariantPropertyOfCocoOrbit: The given group is not a subgroup of the underlying group of the orbit!");
    fi;
    
    stab:=StabilizerOfCanonicalRepresentative(gsorb);
    gs:=CanonicalRepresentativeOfCocoOrbit(gsorb);
    res:=[];
    if IsTrivial(grp) then 
        cosreps:=RightTransversal(ug,stab);
        
        i:=0;signs:=["-","\\","|","/"];
        COCOPrint(" \c");

        for cr in cosreps do 
            if i mod COCORotorMod = 0 then
                COCOPrint("\b",signs[i/COCORotorMod+1],"\c");
            fi;
        
            i:=(i+1) mod (4*COCORotorMod);
            
            ngs:=ActionOfCocoOrbit(gsorb)(gs,cr);
            if func(ngs) then
                ngs:=ConstructorOfCocoOrbitNC(gsorb)(grp,ngs,Group(()));
                
                Add(res,ngs);
            fi;
        od;
        COCOPrint("\b\c");
    elif IsTrivial(stab) then
        cosreps:=RightTransversal(ug,grp);
        
        i:=0;signs:=["-","/","|","\\"];
        COCOPrint(" \c");

        
        for cr in cosreps do 
            if i mod COCORotorMod = 0 then
                COCOPrint("\b",signs[i/COCORotorMod+1],"\c");
            fi;
        
            i:=(i+1) mod (4*COCORotorMod);
            
            ngs:=ActionOfCocoOrbit(gsorb)(gs,cr^-1);
            if func(ngs) then
                ngs:=ConstructorOfCocoOrbit(gsorb)(grp,ngs);
                Add(res,ngs);
            fi;
        od;
        COCOPrint("\b\c");
    elif ValueOption("nodcos")<>fail then # this is buggy! check!
        COCOPrint("xxx\t",Size(ug),"\t",Size(stab),"\t",Size(grp),"\t\c");
        cosreps:=RightTransversal(ug,grp);
        ngs:=ConstructorOfCocoOrbitNC(gsorb)(grp,gs, Intersection(stab,grp));
        
        i:=0;signs:=["-","/","|","\\"];
        COCOPrint(" \c");
        
        for cr in cosreps do 
            if i mod COCORotorMod = 0 then
                COCOPrint("\b",signs[i/COCORotorMod+1],"\c");
            fi;
        
            i:=(i+1) mod (4*COCORotorMod);
            
            if func(ActionOfCocoOrbit(gsorb)(gs,cr)) then
                Add(res, OnCocoOrbits(ngs,cr));
            fi;
        od;
        COCOPrint("\b\c");
    else
        COCOPrint("***\t",Size(ug),"\t",Size(stab),"\t",Size(grp),"\t\c");
            
        cosreps:=List(DoubleCosetRepsAndSizes(ug,stab,grp), x->x[1]);
        COCOPrint(Length(cosreps),"\n");
                      
        ngs:=ConstructorOfCocoOrbitNC(gsorb)(grp,gs, Intersection(stab,grp));
        res:=List(cosreps, x->OnCocoOrbits(ngs,x));
        res:=Filtered(res, x->func(Representative(x)));
    fi;
    
    
    if Length(res)>0 then
        Info(InfoCOCO,2,"+++\t",Size(gsorb),"\t",Size(grp),"\t",Length(res),"\n");
    else
        Info(InfoCOCO, 2,"-\c");
    fi;
    
    return Set(res);
end);

InstallMethod(SubOrbitsOfCocoOrbit,
        "for all coco orbits",
        [IsPermGroup, IsCocoOrbit],
function(grp,gsorb)
    local  ug, stab, gs, res, cosreps, i, signs, cr, ngs;

    return SubOrbitsWithInvariantPropertyOfCocoOrbit(grp,gsorb, ReturnTrue);
end);



InstallMethod(FirstSubOrbitWithInvariantPropertyOfCocoOrbit,
        "for coco-orbits",
        [IsPermGroup, IsCocoOrbit, IsFunction],
function(grp,orb,func)
    local  ug, stab, cosreps, rep, nrep, res;

    ug:=UnderlyingGroupOfCocoOrbit(orb);

    if not IsSubgroup(ug,grp) then
        Error("SubOrbitsWithInvariantPropertyOfCocoOrbit: The given group is not a subgroup of the underlying group of the orbit!");
    fi;

    stab:=StabilizerOfCanonicalRepresentative(orb);
    cosreps:=List(DoubleCosetsNC(ug,stab,grp), Representative); 
    rep:=CanonicalRepresentativeOfCocoOrbit(orb);
    nrep:=ConstructorOfCocoOrbitNC(orb)(grp,rep, Intersection(stab,grp));
    res:=List(cosreps, x->OnCocoOrbits(nrep,x));
    return First(res, x->func(CanonicalRepresentativeOfCocoOrbit(x)));
end);



InstallMethod(\=,
        "for coco orbits",
        IsIdenticalObj,
        [IsCocoOrbit,IsCocoOrbit],
function(orb1,orb2)
    return CanonicalRepresentativeOfCocoOrbit(orb1)=CanonicalRepresentativeOfCocoOrbit(orb2);
end);


InstallMethod(\<,
        "for coco orbits",
        IsIdenticalObj,
        [IsCocoOrbit,IsCocoOrbit],
function(orb1,orb2)
    return CanonicalRepresentativeOfCocoOrbit(orb1)<CanonicalRepresentativeOfCocoOrbit(orb2);
end);

InstallMethod(Size,
        "for CocoOrbits",
        [IsCocoOrbit],
function(orb)
    return Size(UnderlyingGroupOfCocoOrbit(orb))/Size(StabilizerOfCanonicalRepresentative(orb));
end);

InstallMethod(AsList,
        "for CocoOrbits",
        [IsCocoOrbit],
function(orb)
    local act;
    act:=ActionOfCocoOrbit(orb);
    
    return Orbit(UnderlyingGroupOfCocoOrbit(orb), CanonicalRepresentativeOfCocoOrbit(orb), act);
end);

InstallMethod(AsSet,
        "for CocoOrbits",
        [IsCocoOrbit],
function(orb)
    return Set(AsList(orb));
end);

InstallMethod(Representative,
        "for CocoOrits",
        [IsCocoOrbit],
function(orb)
    return CanonicalRepresentativeOfCocoOrbit(orb);
end);


InstallMethod(ViewString,
        "for coco orbits",
        [IsCocoOrbit],
        function(x)
    local res;
    res:="<";
    if IsMutable(x) then
        Append(res,"mutable ");
    fi;
    Append(res,"CocoOrbit>");
    return res;
end);
        
