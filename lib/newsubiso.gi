#############################################################################
##
##  newsubiso.gi               COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of SubColorIsomorphism tests and posets
##
#############################################################################




InstallValue(symmetric, "symmetric" );
InstallValue(asymmetric, "asymmetric" );
InstallValue(symmetrized, "symmetrized" );
InstallValue(asymmetrized, "asymmetrized" );

## DegreeInformationOfTensor classifies the colors of a tensor by their
## subdegrees. it returns a list dMs 
## 1) every irreflexive color gets assigned a type
##         a type is a pair [deg, tp], where
##               tp is "symmetric" or "asymmetric"
##               deg is the subdegree (i.e. out-valency) of the color
## 2) the types are collected in the set dMs[1]
## 3) for every type dMs[1][i], dMs[2][i] containes the number
##    of colors of this type
## 4) for every type dMs[1][i], dMs[3][i] contains the list of colors
##    of this type
## 5) for every irreflexive color c, dMs[4][c] contains the index i
##    such that dMs[1][i] is the type of c
InstallGlobalFunction(DegreeInformationOfTensor,
function(T)
    local   colors,  l,  sym,  asym,  i,  dms,  j;
    
    colors:=Difference([1..OrderOfTensor(T)], ReflexiveColors(T));
    
    l:=[];
    sym:=[];
    asym:=[];
    
    for i in colors do
        if i^Mates(T)>=i then
            if i^Mates(T)=i then
                Add(l,[OutValencies(T)[i],symmetric]);
                Add(sym,i);
            else
                Add(l,[OutValencies(T)[i],asymmetric]);
                Add(asym,i);
                Add(asym,i^Mates(T));
                
            fi;
        fi;
    od;
    l:=Collected(l);
    dms:=TransposedMatMutable(l);
    dms[3]:=[];
    
    for i in dms[1] do
        if i[2]=symmetric then
            Add(dms[3], Filtered(sym, x->OutValencies(T)[x]=i[1]));
        else
            Add(dms[3], Filtered(asym, x->OutValencies(T)[x]=i[1]));
        fi;
    od;
    dms[4]:=[];
    for i in [1..Length(dms[3])] do
        for j in dms[3][i] do
            dms[4][j]:=i;
        od;
    od;
    
    return rec( colorTypes:=dms[1],
                multiplicities:=dms[2],
                typeToColors:=dms[3],
                colorToType:=dms[4] );
end);

DeclareRepresentation("IsSymPartialSTCGoodSetRep",
        IsAttributeStoringRep,
        [ 
          "tensor",
          "map",
          "imap",
          "domain",
          "nsupply",
          "set",
          "task",
          "done",
          "supply",
          "cmplFlags",
          "currIdx"
          ]);

# To explain, what this function does, it is useful to consider an example:
# Suppose T has the folowing DegreeInformation:
# [ [ [ 1, "symmetric" ], [ 2, "asymmetric" ], [ 2, "symmetric" ] ], [ 3, 2, 2 ], [ [ 2, 3, 4 ], [ 5, 7, 6, 8 ], [ 9, 10 ] ], [ , 1, 1, 1, 2, 2, 2, 2, 3, 3 ] ]
# Consider the following merging-type:
# [ [ [ 1, "symmetric" ], 2 ], [ [ 2, "symmetric" ], 1 ] ]
# the first term says, that 2 symmetric colors of valency 1 should be merged
# from the degree-information of T we can read, that there are
# altogether 3 symmetric colors of subdegree 1
# later, all mergings up to algebraic automorphisms should be
# enumerated. It will be quicker to enumerate all sets of 3-2
# symmetric colors of valency 1 and then take the complement (among
# the symmetric colors of valency 1)
# this function does this reduction. In this case it will return:
# [ [ [ [ 1, "symmetric" ], 1 ], [ [ 2, "symmetric" ], 1 ] ], [ true, false ], [ 1, 3 ] ]
# the first element of this list is the augmented type.
# the second list contains flags telling, which element of the type
#    was reduced (in this case onle the first)
# the third list shows the positions of the color types in the
#    degree-informaiton of T
InstallGlobalFunction(STCAugmentedSymType,
function(T,type)
    local elm,newType, flag,flags,newelm,pos,positions,dms;

    dms:=DegreeInformationOfTensor(T);
    newType:=[];flags:=[];positions:=[];
    for elm in type do
        pos:=Position(dms.colorTypes,elm[1]);
        if 2*elm[2]>dms.multiplicities[pos] then
            newelm:=[elm[1],dms.multiplicities[pos]-elm[2]];
            flag:=true;
        else
            newelm:=ShallowCopy(elm);
            flag:=false;
        fi;
        Add(newType,newelm);
        Add(flags,flag);
        Add(positions,pos);
        
#        Error("breakpoint 2");
    od;
    return [newType,flags,positions];
end);

InstallGlobalFunction(EmptySymPartialSTCGoodSet,
function(tensor,type)
    local   augType,dms,task,imap,map,dom,i,j,supply,cand,nsupply,currIdx;
    
    augType:=STCAugmentedSymType(tensor,type);
    
    dms:=DegreeInformationOfTensor(tensor);

    supply:=List(dms.typeToColors{augType[3]},Set);
    task:=List(augType[1], x->x[2]);
    
        
    imap:=Concatenation(List(supply, x->Set(x, y->Set([y,y^Mates(tensor)]))));
    map:=[];
    for i in [1..Length(imap)] do
        for j in imap[i] do
            map[j]:=i;
        od;
    od;
    
    currIdx:=1;
    while currIdx <=Length(task) and task[currIdx] = 0 do
        currIdx:=currIdx+1;
    od;
    
    nsupply:=List(supply, cls->Set(cls, x->map[x]));
    if currIdx<=Length(task) then
        dom:=nsupply[currIdx];
    else
        dom:=[];
    fi;
    
    cand:=rec(tensor:=tensor,
              map:=map,
              imap:=imap,
              domain:=dom,
              nsupply:=nsupply,
              set:=List(task, x->[]),
              task:=task,
              done:=ListWithIdenticalEntries(Length(task),0),
              supply:=supply,
              cmplFlags:=augType[2],
              currIdx:=currIdx
              );
    return Objectify(NewType(GoodSetsFamily(tensor), IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep), cand);
end);

    
InstallMethod(ExtendedPartialGoodSet,
        "for symmetric partial good sets in SymPartialSTCoodSetRep",
        [IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep, IsPosInt],
function(cand,i)
    local   ndom,  newIdx,  newdone,  newset,  obj;

    if cand!.done[cand!.currIdx]+1=cand!.task[cand!.currIdx] then
        newIdx:=cand!.currIdx+1;
        while newIdx <= Length(cand!.task) and cand!.task[newIdx]=0 do
            newIdx:=newIdx+1;
        od;
        if newIdx <= Length(cand!.task) then
            ndom:=cand!.nsupply[newIdx];
        else
            ndom:=[];
        fi;
    else
        ndom:=Filtered(cand!.domain, x->x>i);
        newIdx:=cand!.currIdx;
    fi;

    newdone:=ShallowCopy(cand!.done);
    newdone[cand!.currIdx]:=newdone[cand!.currIdx]+1;
    newset:=ShallowCopy(cand!.set);
    newset[cand!.currIdx]:=Union(newset[cand!.currIdx],cand!.imap[i]);


    obj:=rec(tensor:=cand!.tensor,
             map:=cand!.map,
             imap:=cand!.imap,
             supply:=cand!.supply,
             domain:=ndom,
             nsupply:=cand!.nsupply,
             set:=newset,
             task:=cand!.task,
             done:=newdone,
             currIdx:=newIdx,
             cmplFlags:=cand!.cmplFlags);

    return Objectify(NewType(GoodSetsFamily(cand!.tensor), IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep), obj);
end);

InstallMethod(IsExtendiblePartialGoodSet,
        "for symmetric partial good sets in SymPartialSTCoodSetRep",
        [IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep],
function(cand)
    if cand!.currIdx>Length(cand!.task) then
        return false;
    fi;
    if cand!.done[cand!.currIdx]+Length(cand!.domain)<cand!.task[cand!.currIdx] then
        return false;
    fi;
    if ForAll([cand!.currIdx..Length(cand!.task)], i->cand!.done[i]=cand!.task[i]) then
        return false;
    fi;
    
    return true;
end);


InstallMethod(GoodSetFromPartialGoodSet,
     "for symmetric partial good sets in SymPartialSTCoodSetRep",
    [IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep],
function(cand)
    local   set,  i,  res,  part;
    
#    Error("breakpoint2");
    
    if cand!.currIdx<=Length(cand!.task) then
        return fail;
    fi;


    set:=ShallowCopy(cand!.set);
    for i in [1..Length(set)] do
        if cand!.cmplFlags[i] then
            set[i]:=Difference(cand!.supply[i],set[i]);
        fi;
    od;
    set:=Union(set);

    part:=WLBuildSymGoodSetPartition(cand!.tensor,set);
    part:=WLStabil(cand!.tensor,part);
    if part=fail then
        return fail;
    fi;
    return BuildGoodSet(cand!.tensor, set, part.classes);
end);

InstallMethod(DomainOfPartialGoodSet,
        "for symmetric partial good sets in SymPartialSTCoodSetRep",
        [IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep],
function(cand)
     return cand!.domain;
end);

InstallMethod(TensorOfPartialGoodSet,
        "for symmetric partial good sets in SymPartialSTCoodSetRep",
        [IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep],
function(cand)
    return cand!.tensor;
end);

InstallMethod(IMapOfPartialGoodSet,
        "for symmetric partial good sets in SymPartialSTCoodSetRep",
        [IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep],
function(cand)
    return cand!.imap;
end);

InstallMethod(IsEmptyPartialGoodSet,
        "for symmetric partial good sets in SymPartialSTCoodSetRep",
        [IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep],
function(cand)
    return Union(cand!.set)=[];
end);


InstallMethod( ViewString,
        "for symmetric partial good sets in SymPartialSTCoodSetRep",
        [IsSymPartialGoodSet and IsSymPartialSTCGoodSetRep],
function(pgs)
    return Concatenation("<symmetric partial STC good set ", String(pgs!.set), ">");
end);

######################################################################
#
# asymmetric partial STC good sets
#
######################################################################


DeclareRepresentation("IsAsymPartialSTCGoodSetRep",
        IsAttributeStoringRep,
        [ "tensor",
          "map",
          "imap",
          "domain",
          "nsupply",
          "set",
          "task",
          "done",
          "currIdx",
          ]);


InstallGlobalFunction(EmptyAsymPartialSTCGoodSet,
function(T,type)
    local   dms,  supply,  elm, task, map, imap,  pos,  dom,  obj,  i, nsupply;

    dms:=DegreeInformationOfTensor(T);

    
    supply:=[];
    for elm in type do
        pos:=Position(dms.colorTypes,elm[1]);    # the index to the list of colors 
                                                 # of outvalency elm[1] 
        Add(supply, Set(dms.typeToColors[pos])); # the list of colors of outvalency elm[1]
    od;
    task:=List(type, x->x[2]);
    
    imap:=Concatenation(supply);
    map:=[];
    for i in [1..Length(imap)] do
        map[imap[i]]:=i;
    od;
    imap:=List(imap, x->[x]);
    
    nsupply:=List(supply, cls->Set(cls, x->map[x]));
    dom:=nsupply[1];
    
    obj:=rec(
             tensor:=T,
             map:=map,
             imap:=imap,
             domain:=dom,
             nsupply:=nsupply,
             set:=List(task, x->[]),
             task:=task,
             done:=ListWithIdenticalEntries(Length(task),0),
             currIdx:=1,
             );
    return Objectify(NewType(GoodSetsFamily(T), IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep), obj);
end);


InstallMethod(ExtendedPartialGoodSet,
        "for asymmetric partial good sets in AsymPartialSTCGoodSetRep",
        [IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep, IsPosInt],
function(cand,i)
    local   t, ci,  ndom,  newIdx,  newdone,  newset,  obj;


    t:=cand!.tensor;
    ci:=cand!.map[cand!.imap[i][1]^Mates(t)];

    ndom:=ShallowCopy(cand!.domain);
    if cand!.done[cand!.currIdx]+1=cand!.task[cand!.currIdx] then
        newIdx:=cand!.currIdx+1;
        if newIdx <= Length(cand!.task) then
            ndom:=cand!.nsupply[newIdx];
        else
            ndom:=[];
        fi;
    else
        ndom:=Difference(ndom, Set([i,ci]));
        newIdx:=cand!.currIdx;
    fi;
    newdone:=ShallowCopy(cand!.done);
    newdone[cand!.currIdx]:=newdone[cand!.currIdx]+1;
    newset:=ShallowCopy(cand!.set);
    newset[cand!.currIdx]:=Union(newset[cand!.currIdx],Set([cand!.imap[i][1],cand!.imap[ci][1]]));


    obj:=rec(tensor:=cand!.tensor,
             map:=cand!.map,
             imap:=cand!.imap,
             domain:=ndom,
             nsupply:=cand!.nsupply,
             set:=newset,
             task:=cand!.task,
             done:=newdone,
             currIdx:=newIdx);
    
    return Objectify(NewType(GoodSetsFamily(t), IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep), obj);
end);

InstallMethod(IsExtendiblePartialGoodSet,
     "for asymmetric partial good sets in AsymPartialSTCoodSetRep",
    [IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep],
function(cand)
    if cand!.currIdx>Length(cand!.task) then
        return false;
    fi;
    if cand!.done[cand!.currIdx]+Length(cand!.domain)<2*cand!.task[cand!.currIdx] then
        return false;
    fi;
    return true;
end);

InstallMethod(GoodSetFromPartialGoodSet,
     "for asymmetric partial good sets in AsymPartialSTCoodSetRep",
    [IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep],
function(cand)
    local   set,  i,  res,  part;

    if cand!.currIdx<=Length(cand!.task) then
        return fail;
    fi;


    set:=Union(cand!.set);
    set:=[set, OnSets(set, Mates(cand!.tensor))];

    part:=WLBuildAsymGoodSetPartition(cand!.tensor,set);
    part:=WLStabil(cand!.tensor,part);
    if part=fail then
        return fail;
    fi;
    return BuildGoodSet(cand!.tensor, set[1], part.classes);
end);


InstallMethod(DomainOfPartialGoodSet,
        "for asymmetric partial good sets in AsymPartialSTCoodSetRep",
        [IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep],
function(cand)
     return cand!.domain;
end);

InstallMethod(TensorOfPartialGoodSet,
        "for asymmetric partial good sets in AsymPartialSTCoodSetRep",
        [IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep],
function(cand)
    return cand!.tensor;
end);

InstallMethod(IMapOfPartialGoodSet,
        "for asymmetric partial good sets in AsymPartialSTCoodSetRep",
        [IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep],
function(cand)
    return cand!.imap;
end);

InstallMethod(IsEmptyPartialGoodSet,
        "for asymmetric partial good sets in AsymPartialSTCoodSetRep",
        [IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep],
function(cand)
    return Union(cand!.set)=[];
end);


InstallMethod( ViewString,
        "for asymmetric partial good sets in AsymPartialSTCoodSetRep",
        [IsAsymPartialGoodSet and IsAsymPartialSTCGoodSetRep],
function(pgs)
    return Concatenation("<symmetric partial STC good set ", String(pgs!.set), ">");
end);

##########################################################################
#
#
#
##########################################################################

InstallOtherMethod(Sortex,
        "sortex with an alternative ordering",
        [IsList, IsFunction],
function ( list, fun )
    local  perm;
    
    perm:=[1..Length(list)];
    SortParallel(list,perm,fun);
    return PermList(perm)^-1;
end);

# k ist eine positive natuerliche Zahl ms ist ein multiset von
# "gefärbten" natürlichen Zahlen.  Die Funktion findet alle
# Zerlegungen von k in Summanden aus ms.  Das Ergebnis ist eine Liste
# aller Lösungen 
InstallGlobalFunction(STCSearchPartitionsAux,
function(ms, k)
    local maxSummands, maxRest, mset, gcds,Recursion,solutions,sort;
    
    Recursion:=function(partSum, partSolVector, currIdx)
        local i,mi,li,rest,sort;
        
        if partSum=k then
            Add(solutions, ShallowCopy(partSolVector));
            return;
        fi;
        
        rest:=k-partSum;
        
        if rest>maxRest[currIdx] then
            return;
        fi;
        
        if RemInt(rest, gcds[currIdx])<>0 then
            return;
        fi;
        
        mi:=QuoInt(rest, mset[currIdx][1][1]);
        if currIdx=Length(mset) then
            partSolVector[currIdx]:=mi;
            Add(solutions, ShallowCopy(partSolVector));
            partSolVector[currIdx]:=0;
            return;
        fi;
        
        mi:=Minimum(mset[currIdx][2],mi);
        if rest-maxRest[currIdx+1]>0 then
            li:=QuoInt(rest-maxRest[currIdx+1],mset[currIdx][1][1]);
        else
            li:=0;
        fi;
        
        for i in [mi,mi-1..li] do
            partSolVector[currIdx]:=i;
            Recursion(partSum+mset[currIdx][1][1]*i, partSolVector,
                    currIdx+1);
        od;
        
        partSolVector[currIdx]:=0;
        return;
    end;
    
    solutions:=[];
    maxSummands:=List(ms, x->x[1][1]*x[2]);
    
    sort:=Sortex(maxSummands, function(a,b) return a>b;end);
    mset:=Permuted(ms,sort);
    gcds:=List([1..Length(mset)], x->Gcd(List([x..Length(mset)], 
                  y->mset[y][1][1])));
    maxRest:=List([1..Length(maxSummands)],
                  x->Sum(maxSummands{[x..Length(maxSummands)]}));
    
    Recursion(0, ListWithIdenticalEntries(Length(mset),0), 1);
    
    return List(solutions, x->Permuted(x,sort^-1));
end);


InstallGlobalFunction(STCSymmetrizeMSetElement,
function(m)
    if m[1][2]=symmetric then
        return m;
    else
        return [[m[1][1]*2, symmetrized], m[2]];
    fi;
end);

InstallGlobalFunction(STCUnSymmetrizeMSetElement,
function(m)
    if m[1][2]<>symmetrized then
        return m;
    else
        return [[m[1][1]/2, asymmetric], m[2]];
    fi;
end);

InstallGlobalFunction(STCSearchPartitions,
function(ms,k)
    local mset,preres,i,idx,res;
    if k[2]=symmetric then
        mset:=List(ms, STCSymmetrizeMSetElement);
        res:=STCSearchPartitionsAux(mset,k[1]);
    else
        idx:=Filtered([1..Length(ms)], x->ms[x][1][2]=asymmetric);
        mset:=ms{idx};
        if mset=[] then
            return [];
        fi;
        preres:=STCSearchPartitionsAux(mset,k[1]);
        res:=List(preres, x->ListWithIdenticalEntries(Length(ms),0));
        for i in [1..Length(res)] do
            res[i]{idx}:=preres[i];
        od;
    fi;
    return res;
end);

InstallGlobalFunction(STCFitVectors,
function(v,w)
    local idx;
    
    idx:=Filtered([1..Length(w)], x->w[x]<>0);
    return Minimum(List(idx, x->QuoInt(v[x],w[x])));
end);
        
# upperbound ist ein k-dim. Vektor aus natürlichen Zahlen
# supply ist eine Liste von k-dim. Vektoren aus natürlichen Zahlen
# n ist eine positive ganze Zahl
# Die Funktion findet alle n-elementigen Multisets aus Elementen von supply deren
# Summe komponentenweise kleiner als upperbound ist.
# die Lösungen werden als Vektoren zurückgegeben. Die i-te Komponente
# enthält die Vielfachheit von supply[i] 
InstallGlobalFunction(STCBoundedNCombinations,
function(upperbound, supply,n)
    local Recursion,solutions;
    
    Recursion:=function(partSum, rem, partSolVector, currIdx)
        local rest,mi,i;
        if rem=0 then
            Add(solutions, ShallowCopy(partSolVector));
            return;
        fi;
        
        if currIdx>Length(supply) then
            return;
        fi;
        
        
        rest:=upperbound-partSum;
        
        mi:=STCFitVectors(rest, supply[currIdx]);
        mi:=Minimum(mi,rem);
        
        for i in [mi,mi-1..0] do
            partSolVector[currIdx]:=i;
            Recursion(partSum+supply[currIdx]*i, rem-i, partSolVector,
                    currIdx+1);  
        od;
        partSolVector[currIdx]:=0;

        return;
    end;
    
    solutions:=[];
    Recursion(ListWithIdenticalEntries(Length(upperbound),0), n, List(supply, x->0), 1);
    return solutions;
end);

# A multiset is a set of pair (x,n_x) where n_x is a positive integer
# describing the multiplicty of x in the multiset. The pairs are
# called "terms" of the multiset
# The input to this function are two multisets of types of irreflexive
# colors (recall that the type of a color is the ordered pair [d,tp] where d
# is the subdegree of the color and tp is either "symmetric" or
# "asymmetric"). 
# The function constructs all ways how to obtain the types from
# coarseMs by merging the available types in fineMs
# the result is a list of mergings
# mergings are lists of multisets of multisets. 
# More precisely, for every term of coarseMs the merging contains a
# multiset of multiset describing which types of fine multiset to
# merge in order to obtain the given term of coarseMs
# e.g. suppose that we have
# coarseMS [ [ [ 1, "symmetric" ], 1 ], [ [ 2, "symmetric" ], 1 ], [ [ 4, "symmetric" ], 3 ] ]
# fineMS: [ [ [ 1, "symmetric" ], 3 ], [ [ 2, "asymmetric" ], 2 ], [ [ 2, "symmetric" ], 2 ] ]
# then a merging is:
# [ 
#   [ [ [ [ [ 1, "symmetric" ], 1 ] ], 1 ] ], 
#   [ [ [ [ [ 2, "symmetric" ], 1 ] ], 1 ] ], 
#   [ [ [ [ [ 2, "asymmetric" ], 1 ] ], 2 ], [ [ [ [ 1, "symmetric" ], 2 ], [ [ 2, "symmetric" ], 1 ] ], 1 ] ] 
# ]
# note that coarseMS contains [ [ 4, "symmetric" ], 3 ]. That means,
# that there are 3 symmetric colors of subdegree 4
# The thrid element of the merging says that these three relations can
# be obtained by merging colors from findMS in the following way:
# two of the relations can be obtained by taking each time an
# asymmetric pair of colors of subdegree 2 from fineMS
# the third one can be obtained by takin 2 symmetric colors of
# subdegree 1, and one symmetric color of subdegree 2
# In this casem there is also just this one way to obtain coarseMs
# from fineMs as a merging
InstallGlobalFunction(STCMergingsMultiset,
function(coarseMs,fineMs)
    local Recursion, CleanupTriple, solutions;
    
    Recursion:=function(fineMs, partialSol, currIdx)
        local currVal, currMult, partitions,parts,upperbound,newfMs,
              newBound,i,p;
        
        currVal:=coarseMs[currIdx][1];
        currMult:=coarseMs[currIdx][2];
        partitions:=STCSearchPartitions(fineMs, currVal);

        if partitions=[] then return; fi;
        
        upperbound:=List(fineMs, x->x[2]);
        parts:=STCBoundedNCombinations(upperbound, partitions, currMult);
        
        for p in parts do
            partialSol[currIdx]:=[fineMs, partitions, p];
            newBound:=ShallowCopy(upperbound);
            
            for i in [1..Length(p)] do
                newBound:=newBound-p[i]*partitions[i];
            od;
            newfMs:=[];
       
            for i in [1..Length(newBound)] do
                if newBound[i]<>0 then
                    Add(newfMs, [fineMs[i][1], newBound[i]]);
                fi;
            od;
            if newfMs=[] then
                Add(solutions, StructuralCopy(partialSol));
            else
                Recursion(newfMs, partialSol, currIdx+1);
            fi;
        od;
        Unbind(partialSol[currIdx]);
    end;

    CleanupTriple:=function(triple)
        local ms, partition, part,res,i,ii,j;

        ms:=triple[1];
        partition:=triple[2];
        part:=triple[3];
        res:=[];ii:=0;
        for i in [1..Length(part)] do
            if part[i]<>0 then
                Add(res,[[],part[i]]);ii:=ii+1;
                for j in [1..Length(ms)] do
                    if partition[i][j]<>0 then
                        Add(res[ii][1],[ms[j][1],partition[i][j]]);
                    fi;
                od;
            fi;
        od;
        return res;
    end;
    solutions:=[];
    Recursion(fineMs, [],1);
    solutions:=List(solutions, x->List(x, y->CleanupTriple(y)));
    return solutions;
end);




# this function takes a merging (i.e. a list of multisets of multisets)
# and produces the underlying list of sets of multisets.
# i.e., it forgets the multiplicities on the outer level of multisets
# the result is a list of sets of types of mergings.
# note that every type of merging is infact a degree-multiset
# e.g. from the merging:
# [
#   [ [ [ [ [ 1, "symmetric" ], 1 ] ], 1 ] ],
#   [ [ [ [ [ 2, "symmetric" ], 1 ] ], 1 ] ],
#   [ [ [ [ [ 2, "asymmetric" ], 1 ] ], 2 ], [ [ [ [ 1, "symmetric" ], 2 ], [ [ 2, "symmetric" ], 1 ] ], 1 ] ]
# ]
# the function creates
# [
#   [ [ [ [ 1, "symmetric" ], 1 ] ] ],
#   [ [ [ [ 2, "symmetric" ], 1 ] ] ],
#   [ [ [ [ 1, "symmetric" ], 2 ], [ [ 2, "symmetric" ], 1 ] ], [ [ [ 2, "asymmetric" ], 1 ] ] ]
# ]
# these types will be needed when searching for all candidates of
# mergings of colors one scheme to obtain a given color of the other scheme
InstallGlobalFunction(STCSolution2Types,
function(solution)
    local i,j,k,res;
    res:=[];
    for i in [1..Length(solution)] do
        res[i]:=[];
        for j in solution[i] do
            AddSet(res[i], j[1]);
        od;
    od;
    return res;
end);

# STCTest:=function(T1,T2)
#     local cl1,cl2;

#     cl1:=DegreeInformationOfTensor(T1);
#     cl1:=List([1..Length(cl1[1])], x->[cl1[1][x],cl1[2][x]]);
#     cl2:=DegreeInformationOfTensor(T2);
#     cl2:=List([1..Length(cl2[1])], x->[cl2[1][x],cl2[2][x]]);
#     Print(cl1,"\n",cl2,"\n");
#     return STCMergingsMultiset(cl1,cl2);
# end;




# returns the list of all fusion orbits (under the known color
# automorphism group of cgr1) that are color isomorphic to cgr2
InstallMethod( OrbitsOfColorIsomorphicFusions,
        "for two homogeneous WL-stbale color graphs",
        [IsColorGraph and IsWLStableColorGraph and IsHomogeneous, 
         IsColorGraph and IsWLStableColorGraph and IsHomogeneous],
function(cgr1,cgr2)
    local  T1, T2, cl1, cl2, mergings, symTypes, asymTypes, sol, 
           types, i, symgsorbs, type, asymgsorbs, fusorbs, caut;

    if Order(cgr1) <> Order(cgr2) then
        return [];
    fi;
    
    T1:=StructureConstantsOfColorGraph(cgr1);
    T2:=StructureConstantsOfColorGraph(cgr2);

    cl1:=DegreeInformationOfTensor(T1);
    cl1:=TransposedMatMutable([cl1.colorTypes, cl1.multiplicities]);

    cl2:=DegreeInformationOfTensor(T2);
    cl2:=TransposedMatMutable([cl2.colorTypes, cl2.multiplicities]);


    mergings:=STCMergingsMultiset(cl2,cl1);

    if mergings=[] then
        return [];
    fi;

    symTypes:=[]; asymTypes:=[];
    for sol in mergings do
        types:=STCSolution2Types(sol);
        for i in [1..Length(types)] do
            if cl2[i][1][2]=symmetric then
                Append(symTypes,List(types[i],Set));
            else
                Append(asymTypes,List(types[i],Set));
            fi;
        od;
    od;
    
    symgsorbs:=[];
    for type in symTypes do
        Append(symgsorbs, AllGoodSetOrbits(IteratorOfPartialGoodSetOrbits(AutomorphismGroup(T1),EmptySymPartialSTCGoodSet(T1,type))));
    od;
    
    asymgsorbs:=[];
    for type in asymTypes do
        Append(asymgsorbs, AllGoodSetOrbits(IteratorOfPartialGoodSetOrbits(AutomorphismGroup(T1),EmptyAsymPartialSTCGoodSet(T1,type))));
    od;
    
    fusorbs:=AllFusionOrbits(IteratorOfPartialFusionOrbits(Union(symgsorbs,asymgsorbs)));
    
#    Error("brk");
    
    caut:=ColorAutomorphismGroupOnColors(cgr1);
    
    fusorbs:=Union(List(fusorbs, x->SubOrbitsOfCocoOrbit(caut,x)));
    
    return Filtered(fusorbs, x->IsColorIsomorphicColorGraph(cgr2, ColorGraphByFusion(cgr1,Representative(x))));
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

        
