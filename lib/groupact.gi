############################################
##  $Id$
##
##  $Log$
##
############################################

Revision.groupact_gd :=
  "@(#)$Id$";

#############################################################################
##
##  groupact.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of group actions
##
#############################################################################


GroupActionFam := NewFamily("GroupActionFam", IsGroupAction);

DeclareRepresentation( "IsGroupActionRep", IsAttributeStoringRep,
        ["degree",          # number of vertices
         "domain",          # external set with a part of autGroup acting on it
         "schreier",        # complete Schreier vector of Action(domain)
         "representatives"  # orbit representatives of [1..<order>]
        ]);


InstallGlobalFunction(GroupAction,
       function(arg)
   local i,j,k,xset,
         group, domain, xdom, action, inducedGroup, inducedDomain, schreier, rep,
         orbit, generator, numberOfOrbits, image, order, isomorphism, isFullDomain,obj;

   if Length(arg)=1 then
     group:=arg[1];
     domain := [1..LargestMovedPoint(group)];
     action := OnPoints;
     isFullDomain:=false;
   elif Length(arg) = 2 then
       group := arg[1];
       domain := arg[2];
       action := OnPoints;
       isFullDomain:=false;
   elif Length(arg) = 3 then
       group := arg[1];
       domain := arg[2];
       action := arg[3];
       isFullDomain:=false;
   elif Length(arg) >= 4 then
       group := arg[1];
       domain := arg[2];
       action := arg[3];
       isFullDomain := arg[4];
   fi;
   if not IsList(domain) or not IsInternalRep(domain) then   # das bedarf noch einer Diskussion
      isFullDomain:=true;                                    #
   fi;                                                       #

   if not isFullDomain then
       xdom := Concatenation(Orbits(group, domain, action));
       if Length(xdom)>Length(domain) then
         domain:=xdom;
       fi;
   fi;

   xset:=Immutable(ExternalSet(group,domain,action));
   inducedGroup := Action(xset);
   inducedDomain := [1..Size(domain)];
   order := Length(inducedDomain);
   numberOfOrbits := 0;
   schreier := 0*inducedDomain;
   rep := [];
   for i in inducedDomain do
       if schreier[i] = 0 then
           Add(rep, i);
           schreier[i] := -Length(rep);
           orbit := [i];
           for j in orbit do
               for k in [1..Length(GeneratorsOfGroup(inducedGroup))] do
                   image := j^GeneratorsOfGroup(inducedGroup)[k];
                   if schreier[image] = 0 then
                       Add(orbit, image);
                       schreier[image] := k;
                   fi;
               od;
           od;
       fi;
   od;

   obj:=rec(degree  := order,
              domain := xset,
              schreier := MakeImmutable(schreier),                    #
              representatives := MakeImmutable(rep));                  #
   return Objectify(NewType(GroupActionFam, IsGroupActionRep), obj);
end);

InstallMethod(InducedGroupOfGroupAction,
        "for group actions",
        [IsGroupAction and IsGroupActionRep],
function(cobj)
   return Action(cobj!.domain);
end);

InstallMethod(UnderlyingGroupOfGroupAction,
        "for group actions",
        [IsGroupAction and IsGroupActionRep],
function(cobj)
   return ActingDomain(cobj!.domain);
end);

InstallOtherMethod(UnderlyingGroup,
        "for group actions",
        [IsGroupAction],
function(cobj)
   return UnderlyingGroupOfGroupAction(cobj);
end);


InstallMethod(ActionHomomorphismOfGroupAction,
        "for group actions",
        [IsGroupAction and IsGroupActionRep],
function(cobj)
   return ActionHomomorphism(cobj!.domain);
end);

InstallMethod(DomainOfGroupAction,
        "for group actions",
        [IsGroupAction and IsGroupActionRep],
function(cobj)
   return AsList(cobj!.domain);
end);


InstallMethod( DegreeOfGroupAction,
        "for group actions",
        [IsGroupAction and IsGroupActionRep],
function( cobj )
    return cobj!.degree;
end);

InstallOtherMethod( Degree,
        "for group actions",
        [IsGroupAction],
function( cobj )
    return DegreeOfGroupAction(cobj);
end);

InstallMethod(OrbRepsOfGroupAction,
        "for group actions",
        [IsGroupAction and IsGroupActionRep],
function( cobj )
    return cobj!.representatives;
end);

InstallMethod(RepresentativeWordOfGroupAction,
       "for actions",
       [IsGroupAction and IsGroupActionRep, IsPosInt],
function(cobj, point)
    local schreier, generators, repWord, permIdx, preImg;

    schreier := cobj!.schreier;
    generators := GeneratorsOfGroup(InducedGroupOfGroupAction(cobj));

    repWord := [];
    permIdx := schreier[point];
    preImg := point;
    while permIdx > 0 do
        Add(repWord, permIdx);
        preImg := preImg / generators[permIdx];
        permIdx := schreier[preImg];
    od;

    return rec(word := Reversed(repWord),
               representative := preImg,
               orbitNumber := -permIdx);
end);

InstallGlobalFunction(ApplyRepWord,
function(gens,e,w,act)
  local g,res;

  res:=e;
  for g in w do
     res:=act(res,gens[g]);
  od;

  return res;
end);

InstallMethod(OrbitNumber,
    "for group actions",
    [IsGroupAction, IsPosInt],
function( cobj, point )
    local representatives, repWord, rep, orbitNumber;
    repWord := RepresentativeWordOfGroupAction( cobj, point );
    return repWord.orbitNumber;
end);
