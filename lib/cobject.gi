#############################################################################
##
##  cobject.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of coco-objects
##
#############################################################################


############################################
#F  CocoObjectFam
############################################
CocoObjectFam := NewFamily("CocoObjectFam", IsCocoObject);



InstallMethod(AutGroupOfCocoObject,
        "for all coco-objects",
        [IsCocoObject],
function(t)
   return AutGroupOfPbagObject(NewPbagObject(t),KnownGroupOfAutomorphisms(t), PbagInvariant(t,t));
end);


InstallMethod(IsIsomorphicCocoObject,
		"for all coco-objects",
		IsIdenticalObj,
	[IsCocoObject, IsCocoObject],
function(o1,o2)
   return IsomorphismCocoObjects(o1,o2)<>fail;
end);



InstallOtherMethod(AutomorphismGroup,
       "for all coco-objects",
       [IsCocoObject],
function(o)
   return AutGroupOfCocoObject(o);
end);

InstallOtherMethod(Order,
      "for all coco-objects",
      [IsCocoObject],
function(o)
   return OrderOfCocoObject(o);
end);

InstallMethod(KnownGroupOfAutomorphisms,
   "for coco-objects with known full automorphism group",
   [IsCocoObject and HasAutGroupOfCocoObject],
   50,
function(cgr)
   return AutGroupOfCocoObject(cgr);
end);

InstallGlobalFunction(NewPbagObjectWithInvariantPartition,
function(cobj, part,group)
    local obj,i,v,g;

    obj:=NewPbagObject(cobj);
    obj.part:=part;
    obj.invPart:=[];
    for i in [1..Length(part)] do
       for v in part[i] do
         obj.invPart[v]:=i;
       od;
    od;
    obj.stabChain:=StabChainMutable(group);
    return obj;
end);

InstallGlobalFunction(PbagInvariantWithInvariantPartition,
function(obj)
   local tinv, TestIsomorphism, TestAutomorphism, HashFunction, Invariant;
   tinv:=PbagInvariant(obj,obj);

   TestIsomorphism:=function(TRec1, TRec2, perm)
       return tinv.test(TRec1,TRec2) and OnSetsSets(TRec1.part,perm)=TRec2.part;
   end;

   TestAutomorphism:=function(TRec1, perm)
       return tinv.autTest(TRec1) and OnSetsSets(TRec1.part,perm)=TRec1.part;
   end;

   HashFunction:=function(inv)
       return tinv.hashinv(inv[1])+inv[2]*[1..Length(inv[2])];
   end;

   Invariant:=function(TRec,i)
      local inv1,inv2,j;
      inv1:=tinv.finv(TRec,i);
      inv2:=[];
      for j in TRec.ST do
         if TRec.invPart[j]=TRec.invPart[i] then
            Add(inv2,2);
         else
            Add(inv2,1);
         fi;
      od;
      return [inv1,inv2];
   end;

   return rec(finv    := Invariant,
              hashinv := HashFunction,
              test    := TestIsomorphism,
              autTest := TestAutomorphism);
end);

InstallMethod(IsomorphismCocoObjects,
	"for all coco-objects",
	IsIdenticalObj,
	[IsCocoObject, IsCocoObject],
function(o1,o2)
    local   iso,  kaut1,  kaut2, pbagobjs;

    pbagobjs:=NewPbagObjects(o1,o2);
    iso:=IsomorphismPbagObjects(pbagobjs[1], pbagobjs[2], PbagInvariant(o1,o2));
    if iso=false then
        iso:=fail;
    else
        kaut1:=KnownGroupOfAutomorphisms(o1);
        kaut2:=KnownGroupOfAutomorphisms(o2);

        SetKnownGroupOfAutomorphismsNC(o1, ClosureGroup(kaut1,
                List(GeneratorsOfGroup(kaut2), h->h^(iso^-1))));
        SetKnownGroupOfAutomorphismsNC(o2, ClosureGroup(kaut2,
                List(GeneratorsOfGroup(kaut1), h->h^iso)));
    fi;

   return iso;
end);

InstallMethod(IsomorphismCocoObjectsInGroup,
	"for all coco-objects",
        function(f1,f2,f3) return IsIdenticalObj(f2,f3);end,
	[IsPermGroup, IsCocoObject, IsCocoObject],
function(G,o1,o2)
    local   iso,  kaut1,  kaut2, pbagobjs;

    pbagobjs:=NewPbagObjects(o1,o2);
    iso:=IsomorphismPbagObjectsInGroup(pbagobjs[1], pbagobjs[2], G, PbagInvariant(o1,o2));
    if iso=false then
        iso:=fail;
    fi;
    kaut1:=KnownGroupOfAutomorphisms(o1);
    kaut2:=KnownGroupOfAutomorphisms(o2);

    SetKnownGroupOfAutomorphismsNC(o1, ClosureGroup(kaut1,
            List(GeneratorsOfGroup(kaut2), h->h^(iso^-1))));
    SetKnownGroupOfAutomorphismsNC(o2, ClosureGroup(kaut2,
            List(GeneratorsOfGroup(kaut1), h->h^iso)));

    return iso;
end);

InstallMethod(IsAutomorphismOfObject,
        "for all coco-objects",
        [IsCocoObject, IsPerm],
function(obj,g)
    local   kaut,  inv;

    kaut:=KnownGroupOfAutomorphisms(obj);
    if g in kaut then
        return true;
    fi;

    inv:=PbagInvariant(obj,obj);

    if not inv.autTest(NewPbagObject(obj),g) then
        return false;
    fi;

    SetKnownGroupOfAutomorphismsNC(obj, ClosureGroupCompare(kaut,g));
    return true;
end);

InstallMethod(IsIsomorphismOfObjects,
        "for all coco-objects",
        function(a,b,c) return IsIdenticalObj(a,b);end,
        [IsCocoObject, IsCocoObject, IsPerm],
function(obj1,obj2,g)
    local   inv,  kaut1,  kaut2,pbagobjs;

    inv:=PbagInvariant(obj1,obj2);

    pbagobjs:=NewPbagObjects(obj1,obj2);
    if not inv.test(pbagobjs[1],pbagobjs[2], g) then
        return false;
    fi;

    kaut1:=KnownGroupOfAutomorphisms(obj1);
    kaut2:=KnownGroupOfAutomorphisms(obj2);

    SetKnownGroupOfAutomorphismsNC(obj1, ClosureGroup(kaut1,
            List(GeneratorsOfGroup(kaut2), h->h^(g^-1))));
    SetKnownGroupOfAutomorphismsNC(obj2, ClosureGroup(kaut2,
            List(GeneratorsOfGroup(kaut1), h->h^g)));
    return true;
end);

InstallMethod(SetKnownGroupOfAutomorphisms,
        "for all coco-objects",
        [IsCocoObject, IsPermGroup],
function(obj,grp)
    local   kaut,  gens,  inv,  pbagobj,  g;

    kaut:=KnownGroupOfAutomorphisms(obj);
    gens:=GeneratorsOfGroup(grp);
    gens:=Filtered(gens, g->not(g in kaut));
    if gens=[] then
        return;
    fi;
    inv:=PbagInvariant(obj,obj);
    pbagobj:=NewPbagObject(obj);

    for g in gens do
        if not inv.autTest(pbagobj,g) then
            Error("SetKnownGroupOfAutomorphisms: The given group is not contained in the automorphism group of the CocoObject!");
            return;
        fi;
    od;

    SetKnownGroupOfAutomorphismsNC(obj,grp);
end);
