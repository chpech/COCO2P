
#############################################################################
##
##  colgraph.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation for color graphs
##
#############################################################################


ColorGraphFam := NewFamily("ColorGraphFam", IsColorGraph);

DeclareRepresentation( "IsSchurianCCRep",
        IsAttributeStoringRep,
        ["action",          # a group acting on the vertices of the cgr
         "twoOrbReps",      # representatives of 2-orbits
         "twoOrbitNumbers", # ...[i][w] is the number of the 2-orbit in which [v,w] lies,
                            # where v is the i-th vertex-orbit rep
         "colorNames"       # for each color its name
]);

DeclareRepresentation( "IsColorGraphRep",
        IsAttributeStoringRep,
        ["schurianCC",      # a schurian coherent configuration
         "twoOrbitColors",  # for each rep its color in the cgr
                            # the color is given as index in colorNames
         "colorNames"       # for each color its name
]);


InstallGlobalFunction(ColorGraphByOrbitals,
function(arg)
    local act,obj,ii,i,j,k,l,orbreps;
    act := CallFuncList( GroupAction, arg );
    obj:=rec();
    obj.action:=act;
    obj.twoOrbReps := [];
    obj.twoOrbitNumbers := [];
    k := 0;
    orbreps:=OrbRepsOfGroupAction(act);
    for ii in [1..Length(orbreps)] do
        i := orbreps[ii];
        obj.twoOrbitNumbers[ii] := [];
        for j in Orbits(Stabilizer(InducedGroupOfGroupAction(act), i), [1..DegreeOfGroupAction(act)]) do
            Add(obj.twoOrbReps, [i, j[1]]);
            k := k+1;
            for l in j do
                obj.twoOrbitNumbers[ii][l] := k;
            od;
        od;
    od;

    MakeImmutable(obj.twoOrbReps);
    MakeImmutable(obj.twoOrbitNumbers);

    obj.colorNames:=obj.twoOrbReps;
    obj :=  Objectify(NewType(ColorGraphFam, IsSchurianCCRep), obj);
    SetIsWLStableColorGraph(obj,true);
    SetIsSchurian(obj,true);
    SetOrderOfCocoObject(obj, DegreeOfGroupAction(act));
    SetRankOfColorGraph(obj, Length(obj!.twoOrbReps));
    SetKnownGroups(obj, rec(knownGroupOfAutomorphisms:=InducedGroupOfGroupAction(act)));
    return obj;
end);

InstallGlobalFunction(ColorGraph,
function(arg)
    local sCC, fun, obj, coloring, rep,v,w,colors,i;

    sCC:=CallFuncList( ColorGraphByOrbitals, arg );
    if Length(arg)<=4 then
       return sCC;
    else
       fun:=arg[5];
    fi;

    obj:=rec();
    obj.schurianCC:=sCC;

    coloring := [];
    for i in [1..Rank(sCC)] do
      rep:=ColorRepresentative(sCC,i);
      v:=VertexNamesOfCocoObject(sCC)[rep[1]];
      w:=VertexNamesOfCocoObject(sCC)[rep[2]];
      Add(coloring,fun(v,w));
    od;

    colors:=Set(coloring);
    if Length(colors)=Length(coloring) then
       sCC!.colorNames:=MakeImmutable(coloring);
       return sCC;
    fi;

    coloring:=List(coloring, x->Position(colors,x));

    obj.twoOrbitColors := MakeImmutable(coloring);
    obj.colorNames:=Immutable(colors);
    obj :=  Objectify(NewType(ColorGraphFam, IsColorGraphRep), obj);
    SetOrderOfCocoObject(obj, OrderOfCocoObject(sCC));
    SetRankOfColorGraph(obj, Length(colors));
    SetKnownGroups(obj, rec(knownGroupOfAutomorphisms:=KnownGroupOfAutomorphisms(sCC)));
    return obj;
end);

InstallMethod(ColorMates,
   "for WL-stable color graphs in SchurianCCRep",
   [IsColorGraph and IsWLStableColorGraph],
function(cgr)
   return PermList(List([1..RankOfColorGraph(cgr)], x->ArcColorOfColorGraph(cgr, Reversed(ColorRepresentative(cgr,x)))));
end);

InstallMethod(ArcColorOfColorGraph,
        "for color graphs in SchurianCCRep",
        [IsColorGraph and IsSchurianCCRep, IsPosInt, IsPosInt],
function(cgr , i,j)
    local repWord,gens,nj;
    repWord := RepresentativeWordOfGroupAction(cgr!.action, i);
    gens:=GeneratorsOfGroup(InducedGroupOfGroupAction(cgr!.action));
    nj:=j;
    for i in Reversed(repWord.word) do
        nj := nj/gens[i];
    od;
    return cgr!.twoOrbitNumbers[repWord.orbitNumber][nj];
end);

InstallMethod(ArcColorOfColorGraph,
        "for color graphs in ColorGraphRep",
        [IsColorGraph and IsColorGraphRep, IsPosInt, IsPosInt],
function(cgr, i,j)
    local repWord,gens,nj;
    return cgr!.twoOrbitColors[ArcColorOfColorGraph(cgr!.schurianCC,i,j)];
end);

InstallOtherMethod(ArcColorOfColorGraph,
		"for color graphs",
		[IsColorGraph,IsList],
function(cgr,edge)
   return ArcColorOfColorGraph(cgr,edge[1],edge[2]);
end);


InstallOtherMethod(Rank,
        "for color graphs",
        [IsColorGraph],
function(cgr)
    return RankOfColorGraph(cgr);
end);



InstallMethod(RowOfColorGraph,
        "for color graphs",
        [IsColorGraph, IsPosInt],
function(cgr, i)
    return List([1..Order(cgr)], x -> ArcColorOfColorGraph(cgr, i, x));
end);

InstallMethod(RowOfColorGraph,
      "for color graphs in SchurianCCRep",
      [IsColorGraph and IsSchurianCCRep, IsPosInt],
function(cgr, i)
   local n,repword,row;

   repword:=RepresentativeWordOfGroupAction(cgr!.action,i);
   n:=repword.orbitNumber;
   row:=cgr!.twoOrbitNumbers[n];
   row:=ApplyRepWord(GeneratorsOfGroup(InducedGroupOfGroupAction(cgr!.action)), row, repword.word, Permuted);
   return row;
end);

InstallMethod(RowOfColorGraph,
      "for color graphs in ColorGraphRep",
      [IsColorGraph and IsColorGraphRep, IsPosInt],
function(cgr, i)
   local row;

   row:=RowOfColorGraph(cgr!.schurianCC,i);
   return List(row, x->cgr!.twoOrbitColors[x]);
end);

InstallMethod(ColumnOfColorGraph,
        "for color graphs",
        [IsColorGraph, IsPosInt],
function(cgr, i)
    return List([1..Order(cgr)],  x -> ArcColorOfColorGraph(cgr, x, i));
end);

InstallMethod(ColumnOfColorGraph,
       "for color graphs in SchurianCCRep",
       [IsColorGraph and IsSchurianCCRep, IsPosInt],
function(cgr,i)
   local row,col;

   row:=RowOfColorGraph(cgr,i);
   col:=OnTuples(row, ColorMates(cgr));
   return col;
end);

InstallMethod(ColumnOfColorGraph,
       "for color graphs in ColorGraphRep",
       [IsColorGraph and IsColorGraphRep, IsPosInt],
function(cgr,i)
   local col;

   col:=ColumnOfColorGraph(cgr!.schurianCC,i);
   return List(col, x->cgr!.twoOrbitColors[x]);
end);

InstallMethod(AdjacencyMatrix,
    "for color graphs",
    [IsColorGraph],
function(cgr)
     return List([1..Order(cgr)], x -> List([1..Order(cgr)], y ->
            ArcColorOfColorGraph(cgr, x, y)));
end);

InstallOtherMethod(AdjacencyMatrix,
     "for color graphs and a list of colors",
     [IsColorGraph, IsList],
function(cgr, colors)
    return List([1..Order(cgr)], x->List([1..Order(cgr)], function(y)
        if ArcColorOfColorGraph(cgr,x,y) in colors then
            return 1;
        fi;
        return 0;
    end));
end);


####################
#M BaseGraphOfColorGraph
####################
if TestPackageAvailability("grape","0")=true then
    InstallMethod(BaseGraphOfColorGraph,
            "for color graphs and integers",
            ReturnTrue,
            [IsColorGraph, IsPosInt],
            0,
    function(cgr, color)
        local gamma, twoOrbIdx;
        if not color in [1..Rank(cgr)] then
            return fail;
        fi;
        gamma := Graph(KnownGroupOfAutomorphisms(cgr), [1..Order(cgr)],
                       OnPoints, function(x,y)
            return ArcColorOfColorGraph(cgr, x, y) = color; end, true);
        return gamma;
    end);

    InstallOtherMethod(BaseGraphOfColorGraph,
            "for color graphs and list of integers",
            ReturnTrue,
            [IsColorGraph, IsList],
            0,
    function(cgr, colors)
        local gamma, twoOrbIdx;
        gamma := Graph(KnownGroupOfAutomorphisms(cgr), [1..Order(cgr)],
                       OnPoints, function(x,y)
            return ArcColorOfColorGraph(cgr, x, y) in colors; end, true);
        return gamma;
    end);
fi;

InstallMethod(AlgebraicAutomorphismGroup,
	"for WL-stabil color graphs",
	[IsColorGraph and IsWLStableColorGraph],
function(cgr)
    local t,aaut;
    t := StructureConstantsOfColorGraph(cgr);
    aaut:=AutomorphismGroup(t);
    SetKnownGroupOfAlgebraicAutomorphismsNC(cgr,aaut);
    return aaut;
end);

InstallMethod( ColorRepresentative,
        "for color graphs inSchurianCCRep",
        [IsColorGraph and IsSchurianCCRep, IsPosInt],
function(cgr, i)
   return cgr!.twoOrbReps[i];
end);

InstallMethod( ColorRepresentative,
        "for color graphs in ColorGraphRep",
        [IsColorGraph and IsColorGraphRep, IsPosInt],
function(cgr, color)
    local pos;
    pos := Position(cgr!.twoOrbitColors, color);
    return ColorRepresentative(cgr!.schurianCC,pos);
end);

InstallMethod( Fibres,
        "for color graphs in SchurianCCRep",
        [IsColorGraph and IsSchurianCCRep],
function(cgr)
    local   orbits, grp;

    orbits := Filtered(cgr!.twoOrbReps, x->x[1]=x[2]);
    grp:=InducedGroupOfGroupAction(cgr!.action);
    orbits :=List(orbits, x->Orbit(grp,x[1]));
    return Set(orbits,Set);
end);

InstallMethod( Fibres,
        "for color graphs in ColorGraphRep",
        [IsColorGraph and IsColorGraphRep],
function(cgr)
    local orbits,colors,colorSet,fibres;

    orbits:=Fibres(cgr!.schurianCC);

    colors := List(orbits, x -> ArcColorOfColorGraph(cgr, x[1], x[1]));
    colorSet := Set(colors);
    fibres := List(colorSet, x -> Filtered([1..Length(colors)],  y ->
                      colors[y] = x));
    fibres := List(fibres, x -> Union(orbits{x}));
    return fibres;
end);


InstallMethod( Neighbors,
        "for a color graph, a vertex, and a list of colors",
        [IsColorGraph, IsPosInt, IsList],
function(cgr, x, lcolor)
    local row, result;
    row := RowOfColorGraph(cgr, x);
    result := Filtered([1..Length(row)], y -> row[y] in lcolor);
    return result;
end);

InstallOtherMethod( Neighbors,
        "for a color graph, a vertex, and a color",
        [IsColorGraph, IsPosInt, IsPosInt],
function(cgr, x, color)
    return Neighbors(cgr,x,[color]);
end);

InstallOtherMethod( Neighbors,
        "for a color graph, a list of vertices, and a color",
        [IsColorGraph, IsList, IsPosInt],
function(cgr, lx, color)
    return Intersection(List(lx, x->Neighbors(cgr,x,[color])));
end);

InstallOtherMethod( Neighbors,
        "for a color graph, a list of vertices, and a list of colors",
        [IsColorGraph, IsList, IsList],
function(cgr, lx, lcolor)
    return Intersection(List(lx, x->Neighbors(cgr,x,lcolor)));
end);

InstallMethod(LocalIntersectionArray,
        "for color graphs",
        [IsColorGraph, IsPosInt, IsPosInt],
function(cgr, v,w)
   local i,j,k,mat,row,col,pos;

   k:=ArcColorOfColorGraph(cgr,v,w);
   mat:=List([1..RankOfColorGraph(cgr)], x->ListWithIdenticalEntries(RankOfColorGraph(cgr),0));
   row := RowOfColorGraph(cgr, v);
   col := ColumnOfColorGraph(cgr, w);
   for pos in [1..OrderOfColorGraph(cgr)] do
       i := row[pos];
       j := col[pos];
       mat[i][j]:=mat[i][j]+1;
   od;
   return mat;
end);

InstallOtherMethod(LocalIntersectionArray,
        "for color graphs",
        [IsColorGraph, IsList],
function(cgr, arc)
   return LocalIntersectionArray(cgr,arc[1],arc[2]);
end);


InstallMethod( IsHomogeneous,
        "for a color graph",
        [IsColorGraph],
function(cgr)
    return NumberOfFibres(cgr)=1;
end);

InstallMethod( IsHomogeneous,
        "for a WL-stable color graph",
        [IsColorGraph and IsWLStableColorGraph],
function(cgr)
    return Length(ReflexiveColors(cgr)) = 1;
end);

InstallMethod( IsHomogeneous,
        "for a color graph in SchurianCCRep",
        [IsColorGraph and IsWLStableColorGraph and IsSchurianCCRep],
function(cgr)
    return Length(OrbRepsOfGroupAction(cgr!.action)) = 1;
end);


InstallMethod(IsWLStableColorGraph,
         "for color graphs in ColorGraphRep",
         [IsColorGraph and IsColorGraphRep],
function(cgr)
   local tensor,tor;

   tor:=List([1..Rank(cgr!.schurianCC)], x->ColorRepresentative(cgr!.schurianCC,x));
   tensor:=TensorFromColorReps(cgr,tor);
   if tensor=fail then
      return false;
   else
      SetStructureConstantsOfColorGraph(cgr,tensor);
      SetIsTensorOfCC(tensor,true);
      return true;
   fi;
end);

InstallMethod(StructureConstantsOfColorGraph,
         "for color graphs",
         [IsColorGraph and IsWLStableColorGraph],
function(cgr)
   local reps,tensor;

   reps:=List([1..RankOfColorGraph(cgr)], i->ColorRepresentative(cgr,i));
   tensor:=TensorFromColorReps(cgr,reps);
   SetIsTensorOfCC(tensor,true);
   return tensor;
end);

InstallMethod(VertexNamesOfCocoObject,
          "for color graphs in SchurianCCRep",
          [IsColorGraph and IsSchurianCCRep],
function(cgr)
   return DomainOfGroupAction(cgr!.action);
end);

InstallMethod(VertexNamesOfCocoObject,
         "for color graphs in ColorGraphRep",
         [IsColorGraph and IsColorGraphRep],
function(cgr)
   return VertexNamesOfCocoObject(cgr!.schurianCC);
end);

InstallGlobalFunction(NewPbagObjectForColorGraph,
function(cgr)
    local obj,g;

    obj:=rec();
    obj.T:=cgr;
    obj.v:=OrderOfCocoObject(cgr);
    obj.ncp:=1;
    obj.fvc:=ListWithIdenticalEntries(obj.v,1);
    obj.fcv:=[ [1..obj.v] ];
    obj.S:=[];
    obj.ST:=[];
    g:=KnownGroupOfAutomorphisms(cgr);
    obj.stabChain:=StabChainMutable(g);
    return obj;
end);

InstallMethod(NewPbagObject,
		"for color graphs",
		[IsColorGraph],
function(cgr)
  return NewPbagObjectForColorGraph(cgr);
end);

InstallMethod(NewPbagObjects,
  "for color graphs",
  [IsColorGraph, IsColorGraph],
function(cgr1,cgr2)
  return [NewPbagObjectForColorGraph(cgr1), NewPbagObjectForColorGraph(cgr2)];
end);

InstallGlobalFunction(RowOfCgrObject,
function(obj,v)
  local row;

  if not IsBound(obj.hashtbl) then
     obj.hashtbl:=SparseHashTable@(x->x);
  fi;
  row:=GetHashEntry@(obj.hashtbl,v);
  if row=fail then
     row:=AddHashEntry@(obj.hashtbl, v, RowOfColorGraph(obj.T,v));
  fi;
  return row;
end);

InstallMethod(PbagInvariant,
   "for color graphs",
   [IsColorGraph, IsColorGraph],
function(cgr1,cgr2)
   local TestIsomorphism, TestAutomorphism, Invariant, HashFunction;

   TestIsomorphism:=function(TRec1, TRec2, perm)
       local i,j,row1,row2;

       for i in [1..TRec1.v] do
           row1:=Permuted(RowOfCgrObject(TRec1, i),perm);
           row2:=RowOfCgrObject(TRec2, i^perm);
           if row1<>row2 then
               return false;
           fi;
       od;
       return true;
   end;

   TestAutomorphism:=function(TRec1, perm)
          local i,j,row1,row2;

          for i in [1..TRec1.v] do
              row1:=Permuted(RowOfCgrObject(TRec1, i),perm);
              row2:=RowOfCgrObject(TRec1, i^perm);
              if row1<>row2 then
                  return false;
              fi;
          od;
          return true;
   end;

   Invariant:=function(obj,v)
    local inv,row;

    row:=RowOfCgrObject(obj,v);
    inv:=List(obj.ST, y->row[y]);
    Add(inv, obj.fvc[v]);
    return inv;
end;

   HashFunction:=function(inv)
       return inv*[1..Length(inv)];
   end;

   return rec(finv    := Invariant,
              hashinv := HashFunction,
              test    := TestIsomorphism,
              autTest := TestAutomorphism);
end);


InstallMethod(KnownGroupOfAutomorphisms,
		"for color graphs",
		[IsColorGraph],
function(cgr)
   local kg;

   kg:=KnownGroups(cgr);
   if not IsBound(kg.knownGroupOfAutomorphisms) then
      kg.knownGroupOfAutomorphisms:=Group(());
   fi;
   return kg.knownGroupOfAutomorphisms;
end);


InstallMethod(KnownGroupOfColorAutomorphisms,
		"for color graphs",
		[IsColorGraph and HasColorAutomorphismGroup],
function(cgr)
   return ColorAutomorphismGroup(cgr);
end);


InstallMethod(KnownGroupOfColorAutomorphisms,
		"for color graphs",
		[IsColorGraph],
function(cgr)
   local kg;

   kg:=KnownGroups(cgr);
   if not IsBound(kg.knownGroupOfColorAutomorphisms) then
      kg.knownGroupOfColorAutomorphisms:=Group(());
   fi;
   return kg.knownGroupOfColorAutomorphisms;
end);

InstallMethod(KnownGroupOfColorAutomorphismsOnColors,
		"for color graphs",
		[IsColorGraph],
function(cgr)
   local kg;

   kg:=KnownGroups(cgr);
   if not IsBound(kg.knownGroupOfColorAutomorphismsOnColors) then
      kg.knownGroupOfColorAutomorphismsOnColors:=Group(());
   fi;
   return kg.knownGroupOfColorAutomorphismsOnColors;
end);

InstallMethod(KnownGroupOfAlgebraicAutomorphisms,
		"for color graphs",
		[IsColorGraph and HasAlgebraicAutomorphismGroup],
function(cgr)
   return AlgebraicAutomorphismGroup(cgr);
end);


InstallMethod(KnownGroupOfAlgebraicAutomorphisms,
		"for WL-stable color graphs",
		[IsColorGraph and IsWLStableColorGraph],
function(cgr)
   local kg;

   kg:=KnownGroups(cgr);
   if not IsBound(kg.knownGroupOfAlgebraicAutomorphisms) then
      kg.knownGroupOfAlgebraicAutomorphisms:=Group(());
   fi;
   return kg.knownGroupOfAlgebraicAutomorphisms;
end);

InstallMethod(SetKnownGroupOfAutomorphismsNC,
		"for WL-stable color graphs",
     	[IsColorGraph, IsPermGroup],
function(cgr,g)
   local kg;

   kg:=KnownGroups(cgr);
   kg.knownGroupOfAutomorphisms:=g;
end);

InstallMethod(SetKnownGroupOfColorAutomorphismsNC,
		"for WL-stable color graphs",
     	[IsColorGraph, IsPermGroup],
function(cgr,g)
   local kg;

   kg:=KnownGroups(cgr);
   kg.knownGroupOfColorAutomorphisms:=g;
end);

InstallMethod(SetKnownGroupOfColorAutomorphismsOnColorsNC,
		"for WL-stable color graphs",
     	[IsColorGraph, IsPermGroup],
function(cgr,g)
   local kg;

   kg:=KnownGroups(cgr);
   kg.knownGroupOfColorAutomorphismsOnColors:=g;
end);

InstallMethod(SetKnownGroupOfAlgebraicAutomorphismsNC,
		"for WL-stable color graphs",
     	[IsColorGraph and IsWLStableColorGraph, IsPermGroup],
function(cgr,g)
   local kg;

   kg:=KnownGroups(cgr);
   kg.knownGroupOfAlgebraicAutomorphisms:=g;
end);


InstallMethod(LiftToColorAutomorphism, "for color graphs",
		[IsColorGraph, IsPerm],
function(W,g)
   local xcgr1,xcgr2,res;

   xcgr1:=BuildXCgrObject(W,[1..Rank(W)]);
   xcgr2:=BuildXCgrObject(W,List([1..Rank(W)], i->i^g));
   res:=IsomorphismPbagObjects(xcgr1,xcgr2,XCgrInvariant);
   if res = false then
      return fail;
   fi;
   SetKnownGroupOfColorAutomorphismsNC(W, ClosureGroupCompare(KnownGroupOfColorAutomorphisms(W),res));
   SetKnownGroupOfColorAutomorphismsOnColorsNC(W, ClosureGroupCompare(KnownGroupOfColorAutomorphismsOnColors(W),g));
   return res;
end);

InstallMethod(LiftToColorIsomorphism,
        "for color graphs",
        [IsColorGraph, IsColorGraph, IsPerm],
function(W1,W2,g)
   local xcgr1,xcgr2,res;

   xcgr1:=BuildXCgrObject(W1,List([1..Rank(W1)], i->i^g));
   xcgr2:=BuildXCgrObject(W2,[1..Rank(W2)]);
   res:=IsomorphismPbagObjects(xcgr1,xcgr2,XCgrInvariant);
   if res = false then
      return fail;
   fi;
   return res;
end);


InstallMethod(ColorAutomorphismGroup,
		"for WL-stable color graphs",
		[IsColorGraph and IsWLStableColorGraph],
function(W)
    local S, xcgr1,xcgr2,result, subH,wautv,wautc;

    AutomorphismGroup(W); # KnownGroupOfAutomorphisms(W) is used later on in CheckGroupBuildXCgr
    S:=StabChainMutable(AlgebraicAutomorphismGroup(W));
    xcgr1:=BuildXCgr(W,[1..RankOfColorGraph(W)]);
    xcgr2:=BuildXCgr(W,[1..RankOfColorGraph(W)]);

    result:=[];
    subH:=CheckGroup(xcgr1,xcgr2, S, rec(orbits:=[[1..RankOfColorGraph(W)]], map:=ListWithIdenticalEntries(RankOfColorGraph(W),1)),result);

    wautv:=Group(Concatenation(GeneratorsOfGroup(AutomorphismGroup(W)), result),());
    wautc:=Group(subH.generators,());
    SetColorAutomorphismGroupOnColors(W, wautc);
    SetKnownGroupOfColorAutomorphismsNC(W,wautv);
    SetKnownGroupOfColorAutomorphismsOnColorsNC(W,wautc);
    
    return wautv;
end);


InstallMethod(ColorAutomorphismGroupOnColors,
		"for WL-stable color graphs",
		[IsColorGraph and IsWLStableColorGraph],
function(cgr)
   ColorAutomorphismGroup(cgr); # this sets the attribute ColorAutomorphismGroupOnColors
   return ColorAutomorphismGroupOnColors(cgr); 
end);


InstallOtherMethod(OutValencies,
  "for WL-stable color graphs",
  [IsColorGraph and IsWLStableColorGraph],
function(cgr)
   local reps;
   reps:=List([1..Rank(cgr)], x->ColorRepresentative(cgr,x));
   return List([1..Rank(cgr)], x->Length(Neighbors(cgr,reps[x][1],x)));
end);


InstallMethod(IsUndirectedColorGraph,
   "for color graphs",
   [IsColorGraph],
function(cgr)
   local i,j;

   for i in [1..OrderOfColorGraph(cgr)] do
     for j in [i+1..OrderOfColorGraph(cgr)] do
        if ArcColorOfColorGraph(cgr,i,j)<>ArcColorOfColorGraph(cgr,j,i) then
           return false;
        fi;
     od;
   od;
   return true;
end);


InstallMethod(IsUndirectedColorGraph,
   "for color graphs in SchurianCCRep",
   [IsColorGraph and IsSchurianCCRep],
function(cgr)
   return ColorMates(cgr)=();
end);


InstallMethod(IsUndirectedColorGraph,
   "for color graphs in ColorGraphRep",
   [IsColorGraph and IsColorGraphRep],
function(cgr)
   local mates,asym,c;

   mates:=ColorMates(cgr!.schurianCC);
   asym:=Filtered(MovedPoints(mates), x->x<x^mates);
   for c in asym do
      if cgr!.twoOrbitColors[c]<>cgr!.twoOrbitColors[c^mates] then
         return false;
      fi;
   od;
   return true;
end);


InstallMethod(IsUndirectedColorGraph,
   "for color graphs in SchurianCCRep",
   [IsColorGraph and IsWLStableColorGraph],
function(cgr)
   return ColorMates(cgr)=();
end);


InstallOtherMethod(ReflexiveColors,
     "for WL-stable color graphs",
     [IsColorGraph and IsWLStableColorGraph],
function(cgr)
   return Filtered([1..RankOfColorGraph(cgr)],
      function(x)
         local rep;
         rep:=ColorRepresentative(cgr,x);
         return rep[1]=rep[2];
      end);
end);


InstallMethod(NumberOfFibres,
		"for color graphs",
		[IsColorGraph],
function(cgr)
   return Length(Fibres(cgr));
end);

InstallMethod(NumberOfFibres,
		"for WL-stable color graphs",
		[IsColorGraph and IsWLStableColorGraph],
function(cgr)
   return Length(ReflexiveColors(cgr));
end);


# Let p be a prime, n,d positive integers, such that d divides (p^n-1)
# Let q:=p^n, and let r be a primitive element of GF(q).
# let C be the set of all powers of r^d in GF(q)
# the cyclotomic colored graph Cyc(p,n,d) has as vertices the elements of GF(q)
# the set of colors is given by {*,0,1,...,d-1}
# a pair $(x,y)$ of vertices has color * in Cyc(p,n,d) if x=y. It has
# color i if (x-y) is an element of  C*(r^i)
InstallGlobalFunction(CyclotomicColorGraph,
function(p,n,d)
    local  q, F, r, md, V, gens, pp, g, lab, names, cyccgr;

    if not IsPrimeInt(p) or not IsPosInt(n) or not IsPosInt(d) then
        return fail;
    fi;

    q:=p^n;
    if (q-1) mod d <> 0 then
        return fail;
    fi;

    F:=GF(q);
    r:=PrimitiveElement(F);
    md:=Set([0..(q-1)/d], i->r^(d*i));
    V:=AsSet(F);
    gens:=AsList(CanonicalBasis(AsVectorSpace(GF(p), F)));
    pp:=List(gens, g->PermList(List(V, x->Position(V,x+g))));
    g:=Group(pp);
    lab:=[[Zero(F)]];
    Append(lab,List([0..d-1], x->Set(md*r^x)));
    names:=Concatenation(["*"],[0..d-1]);

    cyccgr:=ColorGraph(g, [1..Length(V)], OnPoints, true, function(a,b) return names[First([1..d+1], i->(V[a]-V[b]) in lab[i])];end);
    return cyccgr;
end);

# function(q,d)
#    local md,V,gens, pp, g, cyccgr,r,lab,names;

#    if not IsPrimePowerInt(q) or not IsPosInt(d) then
#       return fail;
#    fi;

#    if (q^2-1) mod d<>0 then
#       return fail;
#    fi;
#    if ((q^2-1)/d) mod (q-1)<>0 then
#       return fail;
#    fi;

#    V:=AsSet(GF(q^2));
#    md:=Set(Difference(V, [Zero(GF(q^2))]), x->x^d);
#    gens:=AsList(CanonicalBasis(AsVectorSpace(GF(q), GF(q^2))));
#    pp:=List(gens, g->PermList(List(V, x->Position(V,x+g))));
#    g:=Group(pp);
#    cyccgr:=ColorGraph(g, [1..Length(V)], OnPoints, true, function(a,b) return Set(md*(V[a]-V[b]));end);
#    r:=PrimitiveElement(GF(q^2));
#    lab:=List([0..d-1], x->Set(md*r^x));
#    names:=List(ColorNames(cyccgr){[2..Rank(cyccgr)]}, x->Position(lab,x)-1);
#    names:=Concatenation(["*"], names);
#    cyccgr!.colorNames:=names;
#    return cyccgr;
# end);


InstallGlobalFunction(ClassicalCompleteAffineScheme,
function(q)
   local cgr;

   if not IsPrimePowerInt(q) then
      return fail;
   fi;
   cgr:=ColorGraph(Center(GL(2,q)), GF(q)^2, OnRight, true, function(a,b) return NormedRowVector(a-b);end);
   SetIsWLStableColorGraph(cgr,true);
   return cgr;
end);


InstallGlobalFunction(JohnsonScheme,
function(n,k)
   return ColorGraph(SymmetricGroup(n), Combinations([1..n],k), OnSets, true, function(a,b) return Length(Intersection(a,b));end);
end);

InstallMethod(ColorGraphByFusion,
        "for color graphs and for a fusion",
        [IsColorGraph, IsFusionOfTensor],
function(cgr,fusion)
    local T,res;

    T:=StructureConstantsOfColorGraph(cgr);
    if not IsIdenticalObj(FusionFamily(T), FamilyObj(fusion)) then
        Error("The given fusion must belong to the given color graph!");
    fi;
    res:= ColorGraphByFusion(cgr, PartitionOfFusion(fusion));
    SetIsWLStableColorGraph(res,true);
    return res;
end);

#
InstallGlobalFunction(BIKColorGraph,
function(m)
    local  p, maxsingular, i, vert, g, act, cgr;

    p:=v->v{[1..m]}*v{[m+1..2*m]};

    maxsingular:=IdentityMat(2*m,GF(2)){[1..m]};

    vert:=GF(2)^(2*m);
    maxsingular:=SubspaceNC(vert, maxsingular,"base");
    g:=GeneralLinearGroup(m,2);

    act:=function(v,A)
        local v1,v2,res1,res2;
        v1:=v{[1..m]};
        v2:=v{[m+1..2*m]};
        res1:=A*v1;
        res2:=(TransposedMat(A)^(-1))*v2;
        return Concatenation(res1,res2);
    end;

    cgr:= ColorGraph(g, vert, act, true,
    function(v,w)
        local s,f1,f2;
        if v=w then
            return "=";
        fi;
        s:=v+w;
        f1:= p(v+w)=Zero(GF(2));
        if not f1 then
            return "Q-";
        fi;
        f2:= s in maxsingular;
        if f2 then
            return "Q+S+";
        else
            return "Q+S-";
        fi;
    end);
    vert:=VertexNamesOfCocoObject(cgr);

    SetKnownGroupOfAutomorphismsNC(cgr, ClosureGroup(KnownGroupOfAutomorphisms(cgr),
            List(IdentityMat(2*m,GF(2)), x->PermList(List(vert, v->Position(vert, v+x))))));

    SetIsWLStableColorGraph(cgr,true);

    return cgr;
end);

# Q-O- together with Q+S+ give (3,5)-regular srg
InstallGlobalFunction(IvanovColorGraph,
function(m)
    local p,vert,cgr,g,act1,act2,act3,act4;

    p:=v->(v{[1..m]}*v{[m+1..2*m]})+v[m]+v[2*m];

    vert:=AsList(GF(2)^(2*m));
    g:=GeneralLinearGroup(m-1,2);

    act1:=function(v,A)
        local v1,v2,res1,res2;
        v1:=v{[1..m-1]};
        v2:=v{[m+1..2*m-1]};
        res1:=A*v1;
        res2:=(TransposedMat(A)^(-1))*v2;
        return Concatenation(res1,[v[m]],res2,[v[2*m]]);
    end;
    cgr:= ColorGraph(g,vert, act1, true,
    function(v,w)
        local s;

        if v=w then
            return "=";
        fi;
        s:=v+w;
        if ForAll(s{[m..2*m]}, x->x=Zero(GF(2))) then
            return "Q+S+";
        elif ForAll(s{[m+1..2*m-1]}, x->x=Zero(GF(2))) then
            return "Q-O+";
        elif p(s)=Zero(GF(2)) then
            return "Q+S-";
        else
            return "Q-O-";
        fi;
    end);

    SetKnownGroupOfAutomorphismsNC(cgr, ClosureGroup(KnownGroupOfAutomorphisms(cgr), List(IdentityMat(2*m,GF(2)), x->PermList(List(vert, v->Position(vert, v+x))))));

    act2:=function(v,A)
        local res,w;

        w:=A*v{[m,2*m]};
        return Concatenation(v{[1..m-1]},[w[1]],v{[m+1..2*m-1]},[w[2]]);
    end;

    g:=GeneralLinearGroup(2,2);

    SetKnownGroupOfAutomorphismsNC(cgr, ClosureGroup(KnownGroupOfAutomorphisms(cgr), Action(g,vert,act2)));

    act3:=function(v,b)
        local A;
        A:=IdentityMat(2*m,GF(2));
        A{[1..m-1]}{[m+1..2*m-1]}:=DiagonalMat(b);
        A{[1..m-1]}{[2*m]}:=TransposedMat([b]);
        A{[m]}{[m+1..2*m-1]}:=[b];
        return A*v;
    end;

    SetKnownGroupOfAutomorphismsNC(cgr, ClosureGroup(KnownGroupOfAutomorphisms(cgr), List(IdentityMat(m-1,GF(2)),b->Permutation(b,vert,act3))));

    act4:=function(v,d)
        local A;
        A:=IdentityMat(2*m,GF(2));
        A{[1..m-1]}{[m+1..2*m-1]}:=DiagonalMat(d);
        A{[1..m-1]}{[m]}:=TransposedMat([d]);
        A{[2*m]}{[m+1..2*m-1]}:=[d];
        return A*v;
    end;

    SetKnownGroupOfAutomorphismsNC(cgr, ClosureGroup(KnownGroupOfAutomorphisms(cgr), List(IdentityMat(m-1,GF(2)),d->Permutation(d,vert,act4))));


    SetIsWLStableColorGraph(cgr,true);

    return cgr;
end);


InstallOtherMethod(ColorGraphByFusion,
        "for a color graph and a partition of the colors",
        [IsColorGraph, IsList],
function(cgr,part)
   return ColorGraph(KnownGroupOfAutomorphisms(cgr), [1..Order(cgr)], OnPoints, true,
              function(a,b) return Filtered(part, x->ArcColorOfColorGraph(cgr,a,b) in x);end);
end);

InstallGlobalFunction(ColorGraphByMatrix,
function(m)
    return ColorGraph(Group(()),[1..Length(m)], OnPoints, true, function(a,b) return m[a][b];
    end);
end);


InstallMethod(QuotientColorGraph,
        "for a color graph and a vertex-partition",
        [IsColorGraph, IsSet],
function(cgr,part)
  local g;

  g:=Stabilizer(KnownGroupOfAutomorphisms(cgr),part,OnSetsSets);
  return ColorGraph(g, part, OnSets, true,
                      function(v,w) return Set(Concatenation(List(v, x->List(w, y->ArcColorOfColorGraph(cgr,x,y))))); end);
end);


InstallMethod(ColorNames,
        "for color graphs",
        [IsColorGraph],
function(cgr)
   return cgr!.colorNames;
end);

InstallOtherMethod(IsPrimitive,
        "for color graphs",
        [IsColorGraph and IsWLStableColorGraph],
function(cgr)
    if not IsHomogeneous(cgr) then
        return false;
    fi;
    return IsPrimitive(StructureConstantsOfColorGraph(cgr));
end);


InstallMethod(IsSchurian, "for WL-stable color graphs",
		[IsColorGraph and IsWLStableColorGraph],
function(cgr)
    local orbs;

    orbs:=List(Orbits(AutGroupOfCocoObject(cgr),[1..OrderOfColorGraph(cgr)]), Representative);
    return Sum(List(orbs, x->Length(Orbits(Stabilizer(AutGroupOfCocoObject(cgr),x),[1..OrderOfColorGraph(cgr)]))))=RankOfColorGraph(cgr);
#    return RankAction(AutGroupOfCocoObject(cgr),[1..OrderOfColorGraph(cgr)])=RankOfColorGraph(cgr);
end);


InstallMethod(\=,
		"for color graphs",
	[IsColorGraph, IsColorGraph],
function(cgr1,cgr2)
   local names1,names2,vertexmap,cnames1,cnames2,colormap,i,j,pos,row1,row2;

   if OrderOfColorGraph(cgr1)<>OrderOfColorGraph(cgr2) then
      return false;
   fi;

   if RankOfColorGraph(cgr1)<>RankOfColorGraph(cgr2) then
      return false;
   fi;

   names1:=VertexNamesOfCocoObject(cgr1);
   names2:=VertexNamesOfCocoObject(cgr2);
   vertexmap:=[];
   for i in [1..Length(names1)] do
      pos:=Position(names2,names1[i]);
      if pos=fail then
         return false;
      fi;
      vertexmap[i]:=pos;
   od;
   vertexmap:=PermList(vertexmap);

   cnames1:=ColorNames(cgr1);
   cnames2:=ColorNames(cgr2);
   colormap:=[];
   for i in [1..Length(cnames1)] do
      pos:=Position(cnames2,cnames1[i]);
      if pos=fail then
         return false;
      fi;
      colormap[i]:=pos;
   od;
   colormap:=PermList(colormap);

   for i in [1..OrderOfColorGraph(cgr1)] do
      row1:=RowOfColorGraph(cgr1,i);
      row2:=RowOfColorGraph(cgr2,i^vertexmap);
      for j in [1..OrderOfColorGraph(cgr1)] do
         if row1[j]^colormap<>row2[j^vertexmap] then
            return false;
         fi;
      od;
   od;
   return true;
end);


InstallMethod(IsomorphismCocoObjects,
		"for color graphs",
		IsIdenticalObj,
	[IsColorGraph, IsColorGraph],
function(cgr1,cgr2)
    local   cnames1,  cnames2,  colormap,  i,  pos,  xcgr1,  xcgr2,
            res,  kaut1,  kaut2;

   cnames1:=ColorNames(cgr1);
   cnames2:=ColorNames(cgr2);
   colormap:=[];
   for i in [1..Length(cnames1)] do
      pos:=Position(cnames2,cnames1[i]);
      if pos=fail then
         return fail;
      fi;
      colormap[i]:=pos;
   od;
   xcgr1:=BuildXCgrObject(cgr1,colormap);
   xcgr2:=BuildXCgrObject(cgr2,[1..RankOfColorGraph(cgr2)]);
   res:=IsomorphismPbagObjects(xcgr1,xcgr2,XCgrInvariant);
   if res = false then
      return fail;
   fi;
    kaut1:=KnownGroupOfAutomorphisms(cgr1);
    kaut2:=KnownGroupOfAutomorphisms(cgr2);

    SetKnownGroupOfAutomorphismsNC(cgr1, ClosureGroup(kaut1,
            List(GeneratorsOfGroup(kaut2), h->h^(res^-1))));
    SetKnownGroupOfAutomorphismsNC(cgr2, ClosureGroup(kaut2,
            List(GeneratorsOfGroup(kaut1), h->h^res)));
   return res;
end);

InstallMethod(IsIsomorphismOfObjects,
		"for color graphs",
		function(a,b,c) return IsIdenticalObj(a,b);end,
	[IsColorGraph, IsColorGraph, IsPerm],
function(cgr1,cgr2,g)
    local   cnames1,  cnames2,  colormap,  i,  pos,  xcgr1,  xcgr2,
            res,  kaut1,  kaut2;

   cnames1:=ColorNames(cgr1);
   cnames2:=ColorNames(cgr2);
   colormap:=[];
   for i in [1..Length(cnames1)] do
      pos:=Position(cnames2,cnames1[i]);
      if pos=fail then
         return false;
      fi;
      colormap[i]:=pos;
   od;
   xcgr1:=BuildXCgrObject(cgr1,colormap);
   xcgr2:=BuildXCgrObject(cgr2,[1..RankOfColorGraph(cgr2)]);
   if not XCgrInvariant.test(xcgr1,xcgr2,g) then
       return false;
   fi;

    kaut1:=KnownGroupOfAutomorphisms(cgr1);
    kaut2:=KnownGroupOfAutomorphisms(cgr2);


    SetKnownGroupOfAutomorphismsNC(cgr1, ClosureGroup(kaut1,
            List(GeneratorsOfGroup(kaut2), h->h^(g^-1))));
    SetKnownGroupOfAutomorphismsNC(cgr2, ClosureGroup(kaut2,
            List(GeneratorsOfGroup(kaut1), h->h^g)));
    return true;
end);

InstallMethod(IsColorIsomorphismOfColorGraphs,
		"for color graphs",
		function(a,b,c,d) return IsIdenticalObj(a,b) and IsIdenticalObj(c,d);end,
	[IsColorGraph, IsColorGraph, IsPerm, IsPerm],
function(cgr1,cgr2,gv,gc)
    local u,v,kaut1,kaut2;
        
    for u in [1..Order(cgr1)] do
        for v in [1..Order(cgr1)] do
            if ArcColorOfColorGraph(cgr1,u,v)^gc<>ArcColorOfColorGraph(cgr2,u^gv,v^gv) then
                return false;
            fi;
        od;
    od;
    kaut1:=KnownGroupOfColorAutomorphisms(cgr1);
    kaut2:=KnownGroupOfColorAutomorphisms(cgr2);

    SetKnownGroupOfColorAutomorphismsNC(cgr1, ClosureGroup(kaut1,
            List(GeneratorsOfGroup(kaut2), h->h^(gv^-1))));
    SetKnownGroupOfColorAutomorphismsNC(cgr2, ClosureGroup(kaut2,
            List(GeneratorsOfGroup(kaut1), h->h^gv)));
    
    kaut1:=KnownGroupOfColorAutomorphismsOnColors(cgr1);
    kaut2:=KnownGroupOfColorAutomorphismsOnColors(cgr2);

    SetKnownGroupOfColorAutomorphismsOnColorsNC(cgr1, ClosureGroup(kaut1,
            List(GeneratorsOfGroup(kaut2), h->h^(gc^-1))));
    SetKnownGroupOfColorAutomorphismsOnColorsNC(cgr2, ClosureGroup(kaut2,
            List(GeneratorsOfGroup(kaut1), h->h^gc)));
    
    return true;
end);

InstallOtherMethod(IsColorIsomorphismOfColorGraphs,
		"for color graphs",
		function(a,b,c) return IsIdenticalObj(a,b);end,
	[IsColorGraph, IsColorGraph, IsList],
function(cgr1,cgr2,ciso)
    return IsColorIsomorphismOfColorGraphs(cgr1,cgr2,ciso[1],ciso[2]);
end);

InstallMethod(IsomorphismCocoObjectsInGroup,
		"for color graphs",
			function(f1,f2,f3) return IsIdenticalObj(f2,f3);end,
	[IsPermGroup, IsColorGraph, IsColorGraph],
function(G, cgr1,cgr2)
    local   cnames1,  cnames2,  colormap,  i,  pos,  xcgr1,  xcgr2,
            res,  kaut1,  kaut2;

    cnames1:=ColorNames(cgr1);
    cnames2:=ColorNames(cgr2);
    colormap:=[];
    for i in [1..Length(cnames1)] do
        pos:=Position(cnames2,cnames1[i]);
        if pos=fail then
            return fail;
        fi;
        colormap[i]:=pos;
    od;
    xcgr1:=BuildXCgrObject(cgr1,colormap);
    xcgr2:=BuildXCgrObject(cgr2,[1..RankOfColorGraph(cgr2)]);
    res:=IsomorphismPbagObjectsInGroup(xcgr1,xcgr2,G,XCgrInvariant);
    if res = false then
        return fail;
    fi;
    kaut1:=KnownGroupOfAutomorphisms(cgr1);
    kaut2:=KnownGroupOfAutomorphisms(cgr2);

    SetKnownGroupOfAutomorphismsNC(cgr1, ClosureGroup(kaut1,
            List(GeneratorsOfGroup(kaut2), h->h^(res^-1))));
    SetKnownGroupOfAutomorphismsNC(cgr2, ClosureGroup(kaut2,
            List(GeneratorsOfGroup(kaut1), h->h^res)));
    return res;
end);

InstallMethod(ColorIsomorphismColorGraphs,
		"for WL-stable color graphs",
		IsIdenticalObj,
	[IsColorGraph and IsWLStableColorGraph, IsColorGraph and IsWLStableColorGraph],
function(cgr1,cgr2)
   local T1,T2,aiso,xcgr1,xcgr2,naiso,res,PrepareStabChains,S,rS;

   PrepareStabChains:=function(S, rS, part)

       if StbcIsTrivialStabChainNode(S) then
           rS.part:=rec(map:=[1..Length(part.map)],
                        orbits:=List([1..Length(part.map)], x->[x]));
           return;
       fi;

       S.part:=StbcRefineOrbits(S,part, OrderOfTensor(T1));
       rS.part:=StbcRefineOrbits(rS, S.part, OrderOfTensor(T1));

       PrepareStabChains(S.stabilizer, rS.stabilizer, S.part);
   end;


   T1:=StructureConstantsOfColorGraph(cgr1);
   T2:=StructureConstantsOfColorGraph(cgr2);
   aiso:=IsomorphismCocoObjects(T1,T2);
   if aiso=fail then
       return fail;
   fi;
   S:=StabChainMutable(AlgebraicAutomorphismGroup(cgr1)); #AutGroupOfCocoObject(T1));
   rS:=StabChainMutable(KnownGroupOfColorAutomorphismsOnColors(cgr1));
   ChangeStabChain(rS, BaseStabChain(S), false);
   
   PrepareStabChains(S,rS,rec(orbits:=[[1..RankOfColorGraph(cgr1)]], map:=ListWithIdenticalEntries(RankOfColorGraph(cgr1),1)));


   xcgr1:=BuildXCgr(cgr1,[1..RankOfColorGraph(cgr1)]);
   xcgr2:=BuildXCgr(cgr2,[1..RankOfColorGraph(cgr2)]);
   res:=[];
   naiso:=FindCosRep(S, rS, xcgr1,xcgr2,aiso, res);
   if naiso=false then
      return fail;
   fi;
   return [res[1],naiso];
end);



InstallMethod(IsColorIsomorphicColorGraph,
		"for color graphs",
		IsIdenticalObj,
	[IsColorGraph, IsColorGraph],
function(cgr1,cgr2);
   return ColorIsomorphismColorGraphs(cgr1,cgr2)<>fail;
end);


InstallMethod(InducedSubColorGraph,
        "for color graphs",
        [IsColorGraph, IsList],
function(cgr,l)
    local sl,g;

    sl:=Set(l);
    g:=Stabilizer(KnownGroupOfAutomorphisms(cgr),sl,OnSets);

    return ColorGraph(g, sl, OnPoints, true, function(v,w)
        return ColorNames(cgr)[ArcColorOfColorGraph(cgr,v,w)];
    end);
end);

InstallMethod(DirectProductColorGraphs,
        "for color graphs",
        [IsColorGraph, IsColorGraph],
function(cgr1,cgr2)
    local  OnVertexPairs, g, c1, c2, v1, v2,p1,p2;

    OnVertexPairs:=function(p,x)
        return [v1[Position(v1,p[1])^(Image(p1,x))],
                v2[Position(v2,p[2])^(Image(p2,x))]];
    end;

    g:=DirectProduct(KnownGroupOfAutomorphisms(cgr1), KnownGroupOfAutomorphisms(cgr2));
    p1:=Projection(g,1);
    p2:=Projection(g,2);

    c1:=ColorNames(cgr1);
    c2:=ColorNames(cgr2);
    v1:=VertexNamesOfCocoObject(cgr1);
    v2:=VertexNamesOfCocoObject(cgr2);

    return ColorGraph(g, Cartesian(v1,v2), OnVertexPairs, true,
                   function(a,b) return [c1[ArcColorOfColorGraph(cgr1,Position(v1,a[1]),Position(v1,b[1]))],
                                         c2[ArcColorOfColorGraph(cgr2,Position(v2,a[2]),Position(v2,b[2]))]]; end);
end);

InstallMethod(WreathProductColorGraphs,
        "for color graphs",
        [IsColorGraph, IsColorGraph],
function(cgr1,cgr2)
    local  OnVertexPairs, g, c1, c2, v1, v2;

    OnVertexPairs:=function(p,x)
        return [v1[Position(v1,p[1]^(Image(Projection(g,1),x)))],
        v2[Position(v2, p[2]^(Image(Projection(g,2),x)))]];
    end;

    g:=DirectProduct(KnownGroupOfAutomorphisms(cgr1), KnownGroupOfAutomorphisms(cgr2));

    c1:=ColorNames(cgr1);
    c2:=ColorNames(cgr2);
    v1:=VertexNamesOfCocoObject(cgr1);
    v2:=VertexNamesOfCocoObject(cgr2);

    return ColorGraph(g, Cartesian(v1,v2), OnVertexPairs, true,
    function(a,b)
        if a[1]<>b[1] then
            return [c1[ArcColorOfColorGraph(cgr1,Position(v1,a[1]),Position(v1,b[1]))], "*"];
        else
            return [c1[ArcColorOfColorGraph(cgr1,Position(v1,a[1]),Position(v1,b[1]))],
                    c2[ArcColorOfColorGraph(cgr2,Position(v2,a[2]),Position(v2,b[2]))]];
        fi;
    end);
end);


InstallOtherMethod( ClosedSets,
        "for association schemes",
        [IsColorGraph and IsWLStableColorGraph],
function(cgr);
    return ClosedSets(StructureConstantsOfColorGraph(cgr) );
end);

InstallMethod( PartitionClosedSet,
        "for association schemes",
        [IsColorGraph and IsWLStableColorGraph and IsHomogeneous, IsList],
function(cgr, set )
    local gamma, i;
    gamma := BaseGraphOfColorGraph(cgr, Set(set));
    for i in gamma.representatives do
        RemoveEdgeOrbit(gamma, [i, i]);
    od;
    return ConnectedComponents( gamma );
end);


InstallGlobalFunction(ColorGraphByWLStabilization,
function(cgr)
    local   aut,  scgr,  tor,  part,  i,  c,  h,  spart,  npart,  acl,
            ccounter,  colors,rpart,scl,rcgr;

    if IsWLStableColorGraph(cgr) then
        return cgr;
    fi;

    aut:=KnownGroupOfAutomorphisms(cgr);
    scgr:=ColorGraphByOrbitals(aut,[1..OrderOfColorGraph(cgr)], OnPoints,true);
    tor:=ColorNames(scgr);
    part:=List([1..RankOfColorGraph(cgr)], x->[]);
    for i in [1..Length(tor)] do
        c:=ArcColorOfColorGraph(cgr,tor[i]);
        AddSet(part[c],i);
    od;
    h:=ColorMates(scgr);
    spart:=List(part, x->Intersection(x,OnSets(x,h)));
    rpart:=List(spart, x->Intersection(x, ReflexiveColors(scgr)));

    npart:=[];
    for i in [1..Length(part)] do
        if spart[i]<>[] then
            acl:=Difference(part[i],spart[i]);
            if acl<>[] then
                Add(npart,acl);
            fi;

            if rpart[i]<>[] then
                Add(npart,rpart[i]);
                scl:=Difference(spart[i],rpart[i]);
                if scl<>[] then
                    Add(npart, scl);
                fi;
            else
                Add(npart, spart[i]);
            fi;
        else
            Add(npart,part[i]);
        fi;
    od;
    part:=WLBuildPartition(npart);
    part:=WLStabil(StructureConstantsOfColorGraph(scgr),part);
    if part=fail then
        Error("This is not supposed to hapen!");
    fi;
    # ccounter:=List([1..RankOfColorGraph(cgr)], x->1);
    # colors:=[];
    #
    # for i in [1..Length(part.classes)] do
    #     c:=ArcColorOfColorGraph(cgr,tor[part.classes[i][1]]);
    #     Add(colors,[c,ccounter[c]]);
    #     ccounter[c]:=ccounter[c]+1;
    # od;

    rcgr:=ColorGraph(aut,[1..OrderOfColorGraph(cgr)], OnPoints,true,
    function(u,v)
        local col,cidx;
        col:=ArcColorOfColorGraph(scgr,u,v);
        cidx:=First([1..Length(part.classes)],i->col in part.classes[i]);
        return part.colorNames[cidx];
#        return colors[cidx];
    end);
    SetIsWLStableColorGraph(rcgr,true);
    return rcgr;
end);

InstallGlobalFunction(WLStableColorGraphByMatrix,
function(M)
    local p,res,cgr;

    p:=WLMatBuildPartition(M);
    WLMatStabil(p);
    res:=Sum([1..Length(p.classes)],i->i*p.classes[i][1]);#return p;
    cgr:=ColorGraph(Group(()), [1..Length(M)], OnPoints,true, function(u,v) return p.colorNames[res[u][v]];end);
    SetIsWLStableColorGraph(cgr,true);
    return cgr;
end);




####################
#M ViewString(cgr)
####################
InstallMethod(ViewString,
        "for color graphs",
        [IsColorGraph],
function(x)
    return Concatenation("<", "color graph of order ",
                   String(OrderOfCocoObject(x)), " and rank ",
                   String(RankOfColorGraph(x)), ">");
end);




InstallMethod( Display,
        "for color graphs",
        [IsColorGraph],
        function(cgr)
    local names;

    names:=ColorNames(cgr);
    Display(List(AdjacencyMatrix(cgr),r->List(r, e->names[e])));
end);

InstallMethod( PrintString,
        "for color graphs",
        [IsColorGraph],
        function(cgr)
    local names;
    names:=ColorNames(cgr);
    return PRINT_STRINGIFY("ColorGraphByMatrix( ",
                   List(AdjacencyMatrix(cgr),r->List(r, e->names[e]))," )");
end);

InstallMethod( String,
        "for color graphs",
        [IsColorGraph],
        function(cgr)
    local names;
    names:=ColorNames(cgr);
    return STRINGIFY("ColorGraphByMatrix( ",
                   List(AdjacencyMatrix(cgr),r->List(r, e->names[e]))," )");
end);
