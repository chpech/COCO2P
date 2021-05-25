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
        
