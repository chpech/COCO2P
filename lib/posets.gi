#############################################################################
##
##  posets.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of coco posets        
##
#############################################################################

CocoPosetFam := NewFamily("CocoPosetFam", IsCocoPoset);

DeclareRepresentation( "IsCocoPosetRep", 
        IsAttributeStoringRep,
        ["elements",     # list of all elements of the poset. The list must be
                         # ordered in a way that is compatible with the partial
                         # order relation (no element is preceeded by a greater element). 
         "successors",   # on index i the list of all indices of successors of the
                         # element #i is stored
         "predecessors", # the same as successors for predecessors
         "levels"
         ]);

InstallMethod(SuccessorsInCocoPoset,
        "for COCO-posets",
        [IsCocoPoset and IsCocoPosetRep, IsPosInt],
function(poset, elm)
    return poset!.successors[elm];
end);

InstallOtherMethod(Size,
        "for COCO-posets",
        [IsCocoPoset],
function(poset)
    return Length(ElementsOfCocoPoset(poset));
end);

InstallMethod(ElementsOfCocoPoset,
        "for COCO-posets",
        [IsCocoPoset and IsCocoPosetRep],
function(poset)
    return poset!.elements;
end);


InstallMethod(PredecessorsInCocoPoset,
        "for COCO-posets",
        [IsCocoPoset and IsCocoPosetRep, IsPosInt],
function(poset, elm)
    return poset!.predecessors[elm];
end);

InstallMethod(FilterInCocoPoset,
        "for COCO-posets",
        [IsCocoPoset, IsPosInt],
function(poset,elm)
    local filter,succ;
    
    filter:=[elm];
    succ:=[elm];
    repeat
        succ:=Set(Concatenation(List(succ, x->SuccessorsInCocoPoset(poset,x))));
        UniteSet(filter, succ);
    until succ=[];
    return filter;
end);

InstallOtherMethod(FilterInCocoPoset,
        "for COCO-posets",
        [IsCocoPoset, IsSet],
function(pos,m)
   return Union(List(m, x->FilterInCocoPoset(pos,x)));
end);

InstallMethod(IdealInCocoPoset,
        "for COCO-posets",
        [IsCocoPoset, IsPosInt],
function(poset,elm)
    local ideal,pred;
    
    ideal:=[elm];
    pred:=[elm];
    repeat
        pred:=Set(Concatenation(List(pred, x->PredecessorsInCocoPoset(poset,x))));
        UniteSet(ideal, pred);
    until pred=[];
    return ideal;
end);

InstallOtherMethod(IdealInCocoPoset,
        "for COCO-posets",
        [IsCocoPoset, IsSet],
function(pos,m)
   return Union(List(m, x->IdealInCocoPoset(pos,x)));
end);

InstallMethod(MinimalElementsInCocoPoset,
        "for COCO-posets",
        [IsCocoPoset, IsSet],
function(pos,m)
   return Filtered(m, x->Intersection(IdealInCocoPoset(pos,x),m)=[x]);
end);

InstallMethod(MaximalElementsInCocoPoset,
        "for COCO-posets",
        [IsCocoPoset, IsSet],
function(pos,m)
   return Filtered(m, x->Intersection(FilterInCocoPoset(pos,x),m)=[x]);
end);

InstallMethod(InducedCocoPoset,
        "for COCO-posets",
        [IsCocoPoset, IsCocoPoset and IsCocoPosetRep, IsSet],
function(filter,pos,m)
    local map,i,newpos,x,flt,id,succ,pred;
   
    map:=[];
    for i in [1..Length(m)] do
        map[m[i]]:=i;
    od;
    
    newpos:=rec();
    newpos.elements:=m;
    newpos.successors:=List(m,x->[]);
    newpos.predecessors:=List(m, x->[]);
    for x in m do
        flt:=FilterInCocoPoset(pos,x);
        RemoveSet(flt,x);
        succ:=Union(MinimalElementsInCocoPoset(pos,Intersection(flt,m)), Intersection(SuccessorsInCocoPoset(pos,x),m));
        newpos.successors[map[x]]:=List(succ, x->map[x]);
        id:=IdealInCocoPoset(pos,x);
        RemoveSet(id,x);
        pred:=MaximalElementsInCocoPoset(pos, Intersection(id,m));
        newpos.predecessors[map[x]]:=List(pred, x->map[x]);
    od;
  
   return Objectify(NewType(CocoPosetFam, IsCocoPosetRep), newpos);
end);

InstallOtherMethod(InducedCocoPoset,
        "for COCO-posets",
        [IsCocoPoset, IsSet],
function(pos,set)
    return InducedCocoPoset(IsCocoPoset, pos,set);
end);

    
InstallGlobalFunction(CocoPosetByFunctions,
function(elements,order,linorder)
    local   poset,  i,  active,  j;
    
    Sort(elements, linorder);
    
    poset:=rec();
    poset.elements:=Immutable(elements);
    poset.successors:=List(elements, x->[]);
    poset.predecessors:=List(elements,x->[]);
    poset:=Objectify(NewType(CocoPosetFam, IsCocoPosetRep), poset);
    
    for i in [Length(elements),Length(elements)-1..1] do
        active:=[i+1..Length(elements)];
        while active<>[] do
            j:=active[1]; active:=active{[2..Length(active)]};
            if order(elements[i],elements[j]) then
                Add(poset!.successors[i],j);
                Add(poset!.predecessors[j],i);
                SubtractSet(active,FilterInCocoPoset(poset,j));
            fi;
        od;
    od;
    MakeImmutable(poset!.successors);
    MakeImmutable(poset!.predecessors);
    return poset;
    
end);

