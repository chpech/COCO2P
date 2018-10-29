DeclareRepresentation("IsSTCSymGoodSetCandRep",
        IsAttributeStoringRep,
        [ "tensor",            
          "nperm",
          "ndomain", # a list of sets of normalized colors
          "nset",    # a list of sets of already chosen normalized colors
          "task",    # a list of integers giving the goal sizes of the
                     # elements of set
          "done",    # 
          "nsupply", # a list of sets of normalized colors
          "cmplFlags",# list of booleans which part of nset is complemented
          "currIdx", # the current index into nset on which is worked
          ]);

DeclareRepresentation("IsSTCAsymGoodSetCandRep",
        IsAttributeStoringRep,
        [ "tensor",            
          "nperm",
          "ndomain", # a list of sets of normalized colors
          "nset",    # a list of sets of already chosen normalized colors
          "task",    # a list of integers giving the goal sizes of the
                     # elements of set
          "done",    # 
          "nsupply", # a list of sets of normalized colors
          "currIdx", # the current index into nset on which is worked
          ]);



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
    
    return dms;
end);

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
        pos:=Position(dms[1],elm[1]);
        if 2*elm[2]>dms[2][pos] then
            newelm:=[elm[1],dms[2][pos]-elm[2]];
            flag:=true;
        else
            newelm:=ShallowCopy(elm);
            flag:=false;
        fi;
        Add(newType,newelm);
        Add(flags,flag);
        Add(positions,pos);
    od;
    return [newType,flags,positions];
end);

InstallGlobalFunction(STCEmptySymGoodSetCand,
function(T,augType)
    local   dms,  supply,  dom,  np,  clr,  obj,  ci;
    dms:=DegreeInformationOfTensor(T);

    supply:=List(dms[3]{augType[3]},Set);
    dom:=List(supply, x->Filtered(x,x->x^Mates(T)>=x));
    np:=List(dom, x->Filtered(x,x->x^Mates(T)>=x));
    clr:=Difference([1..OrderOfTensor(T)], ReflexiveColors(T));

    np:=Concatenation(List(np, x->Concatenation(List(x,y->Set([y,y^Mates(T)])))));
    Append(np, Difference(clr,Set(np)));
    np:=Concatenation(ReflexiveColors(T),np);

    np:=PermList(np)^-1;
    obj:=rec(
             tensor:=T,
             nperm:=np,
             nsupply:=OnTuplesSets(supply,np),
             ndomain:=OnTuplesSets(dom,np),
             nset:=List(supply, x->[]),
             task:=List(augType[1], x->x[2]),
             done:=List(augType[1], x->0),
             currIdx:=1,
             cmplFlags:=augType[2]
             );
    ci:=First([1..Length(obj.task)], i->obj.task[i]<>0);
    if ci=fail then
        ci:=Length(obj.task)+1;
    fi;

    obj.currIdx:=ci;


    return Objectify(NewType(GoodSetsFamily(T), IsSymGoodSetCandidate and IsSTCSymGoodSetCandRep), obj);
end);

InstallMethod(ExtendedCandidate,
        "for symmetric candidates in STCSymGoodSetCandRep",
        [IsSymGoodSetCandidate and IsSTCSymGoodSetCandRep, IsPosInt],
function(cand,i)
    local   ci,  mates,  newndom,  newIdx,  newdone,  newnset,  obj,
            nperm,  nsupply,  ndomain,  nset,  task,  done,  currIdx,
            cmplFlags;

    if i in cand!.nset[cand!.currIdx] then
        return cand;
    fi;
    if not i in cand!.ndomain[cand!.currIdx] then
        return fail;
    fi;

    ci:=((i/cand!.nperm)^Mates(cand!.tensor))^cand!.nperm;
    mates:=Set([i,ci]);

    newndom:=ShallowCopy(cand!.ndomain);
    if cand!.done[cand!.currIdx]+1=cand!.task[cand!.currIdx] then
        newndom[cand!.currIdx]:=[];
        newIdx:=cand!.currIdx+1;
    else
        newndom[cand!.currIdx]:=Difference(newndom[cand!.currIdx], [i]);
        newIdx:=cand!.currIdx;
    fi;
    newdone:=ShallowCopy(cand!.done);
    newdone[cand!.currIdx]:=newdone[cand!.currIdx]+1;
    newnset:=ShallowCopy(cand!.nset);
    newnset[cand!.currIdx]:=Union(newnset[cand!.currIdx],mates);


    obj:=rec(tensor:=cand!.tensor,
             nperm:=cand!.nperm,
             nsupply:=cand!.nsupply,
             ndomain:=newndom,
             nset:=newnset,
             task:=cand!.task,
             done:=newdone,
             currIdx:=newIdx,
             cmplFlags:=cand!.cmplFlags);

    return Objectify(NewType(GoodSetsFamily(cand!.tensor), IsSymGoodSetCandidate and IsSTCSymGoodSetCandRep), obj);
end);


InstallMethod(TestCandidate,
    "for symmetric candidates in STCSymGoodSetCandRep",
    [IsSymGoodSetCandidate and IsSTCSymGoodSetCandRep],
function(cand)
    local   nset,  i,  set,  res,  part;

    if cand!.currIdx<=Length(cand!.nsupply) then
        return [];
    fi;


    nset:=ShallowCopy(cand!.nset);
    for i in [1..Length(nset)] do
        if cand!.cmplFlags[i] then
            nset[i]:=Difference(cand!.nsupply[i],nset[i]);
        fi;
    od;
    nset:=Union(nset);
    set:=OnSets(nset,cand!.nperm^-1);

    res:=[];
    part:=WLBuildSymGoodSetPartition(cand!.tensor,set);
    part:=WLStabil(cand!.tensor,part);
    if part<> fail then
        res:=[[set],part];
    fi;

    return res;
end);

InstallMethod(IsExtendibleCandidate,
    "for symmetric candidates in STCSymGoodSetCandRep",
    [IsSymGoodSetCandidate and IsSTCSymGoodSetCandRep],
function(cand)
    if cand!.currIdx>Length(cand!.nsupply) then
        return false;
    fi;
    if cand!.done[cand!.currIdx]+Length(cand!.ndomain[cand!.currIdx])<cand!.task[cand!.currIdx] then
        return false;
    fi;
    return true;
end);



InstallGlobalFunction(STCEmptyAsymGoodSetCand,
function(T,type)
    local   dms,  supply,  elm,  pos,  dom,  np,  clr,  obj;

    dms:=DegreeInformationOfTensor(T);


    supply:=[];
    for elm in type do
        pos:=Position(dms[1],elm[1]);
        Add(supply, Set(dms[3][pos]));
    od;


    dom:=supply;
    np:=List(dom, x->Filtered(x,x->x^Mates(T)>x));
    clr:=Difference([1..OrderOfTensor(T)], ReflexiveColors(T));

    np:=Concatenation(List(np, x->Concatenation(List(x,y->[y,y^Mates(T)]))));
    Append(np, Difference(clr,Set(np)));
    np:=Concatenation(ReflexiveColors(T),np);

    np:=PermList(np)^-1;
    obj:=rec(
             tensor:=T,
             nperm:=np,
             nsupply:=OnTuplesSets(supply,np),
             ndomain:=OnTuplesSets(dom,np),
             nset:=List(supply, x->[]),
             task:=List(type, x->x[2]),
             done:=List(type, x->0),
             currIdx:=1,
             );
    return Objectify(NewType(GoodSetsFamily(T), IsAsymGoodSetCandidate and IsSTCAsymGoodSetCandRep), obj);
end);

InstallMethod(ExtendedCandidate,
        "for asymmetric candidates in STCSymGoodSetCandRep",
        [IsAsymGoodSetCandidate and IsSTCAsymGoodSetCandRep, IsPosInt],
function(cand,i)
    local   ci,  mates,  newndom,  newIdx,  newdone,  newnset,  obj;


   if i in cand!.nset[cand!.currIdx] then
       return cand;
   fi;

   if ((i/cand!.nperm)^Mates(cand!.tensor))^cand!.nperm in cand!.nset[cand!.currIdx] then
       return fail;
   fi;

   if not i in cand!.ndomain[cand!.currIdx] then
      return fail;
   fi;

   ci:=((i/cand!.nperm)^Mates(cand!.tensor))^cand!.nperm;
   mates:=Set([i,ci]);

   newndom:=ShallowCopy(cand!.ndomain);
   if cand!.done[cand!.currIdx]+1=cand!.task[cand!.currIdx] then
       newndom[cand!.currIdx]:=[];
       newIdx:=cand!.currIdx+1;
   else
       newndom[cand!.currIdx]:=Difference(newndom[cand!.currIdx], mates);
       newIdx:=cand!.currIdx;
   fi;
   newdone:=ShallowCopy(cand!.done);
   newdone[cand!.currIdx]:=newdone[cand!.currIdx]+1;
   newnset:=ShallowCopy(cand!.nset);
   newnset[cand!.currIdx]:=Union(newnset[cand!.currIdx],[i]);


   obj:=rec(tensor:=cand!.tensor,
            nperm:=cand!.nperm,
            nsupply:=cand!.nsupply,
            ndomain:=newndom,
            nset:=newnset,
            task:=cand!.task,
            done:=newdone,
            currIdx:=newIdx);

   return Objectify(NewType(GoodSetsFamily(cand!.tensor), IsAsymGoodSetCandidate and IsSTCAsymGoodSetCandRep), obj);
end);

InstallMethod(TestCandidate,
    "for asymmetric candidates in STCAsymGoodSetCandRep",
    [IsAsymGoodSetCandidate and IsSTCAsymGoodSetCandRep],
function(cand)
    local   nset,  set,  res,  part;

    if cand!.currIdx<=Length(cand!.nsupply) then
        return [];
    fi;


    nset:=Union(cand!.nset);
    set:=OnSets(nset,cand!.nperm^-1);
    set:=[set, OnSets(set, Mates(cand!.tensor))];
    res:=[];
    part:=WLBuildAsymGoodSetPartition(cand!.tensor,set);
    part:=WLStabil(cand!.tensor,part);
    if part<> fail then
        res:=[set,part];
    fi;

    return res;
end);

InstallMethod(IsExtendibleCandidate,
    "for asymmetric candidates in STCAsymGoodSetCandRep",
    [IsAsymGoodSetCandidate and IsSTCAsymGoodSetCandRep],
function(cand)
    if cand!.currIdx>Length(cand!.nsupply) then
        return false;
    fi;
    if cand!.done[cand!.currIdx]+Length(cand!.ndomain[cand!.currIdx])/2<cand!.task[cand!.currIdx] then
        return false;
    fi;
    return true;
end);

InstallGlobalFunction(STCAsymGSReps,
function(GT,T,type)
    local h,G,S,cand,dom,firsts,result,i,Si,part,ncand;

    cand:=STCEmptyAsymGoodSetCand(T,type);

    h:=NormalizingPermutationOfCandidate(cand);
    G:=GT^h;
    S:=Stbc(G);

    dom:=NormalizedDomainOfCandidate(cand);
    firsts:=StbcMinimalOrbitReps(S,dom);
    firsts:=Filtered(firsts, x->x<((x/h)^Mates(T))^h);
    result:=[];
    for i in firsts do
        ncand:=ExtendedCandidate(cand,i);
        Si:=StbcStabilizer(S,i);

        part:=TestCandidate(ncand);

        if part<>[] then
#            Print(",\c");
            Add(result, [StbcGroup(Si)^(h^-1),part[1],part[2].classes]);
        fi;

        if IsExtendibleCandidate(ncand) then
            Append(result, List(ExtendAsymGSCand(S,Si,ncand), x->[StbcGroup(x[1])^(h^-1), x[2], x[3]]));
        fi;

    od;
    return result;
end);

InstallGlobalFunction(STCSymGSReps,
function(GT,T,type)
    local   cand,  h,  G,  S,  part,  reps;

    cand:=STCEmptySymGoodSetCand(T, STCAugmentedSymType(T,type));

    h:=NormalizingPermutationOfCandidate(cand);
    G:=GT^h;
    S:=Stbc(G);
    part:=TestCandidate(cand);
    reps:=[];

    if part<>[] then
        Add(reps,[S,part[1],part[2].classes]);
#        Print(".\c");
    fi;
    if IsExtendibleCandidate(cand) then
        Append(reps, ExtendSymGSCand(S, StbcCopy(S), cand));
    fi;

    reps:=List(reps, x->[StbcGroup(x[1])^(h^-1), x[2], x[3]]);

    return reps;
end);

InstallGlobalFunction(STCGoodSetReps,
function(G,T,symTypes,asymTypes)
    local  ags, i, sgs, lgs;

    if not ForAll(GeneratorsOfGroup(G), g->IsAutomorphismOfObject(T,g)) then
        Error("AllGoodSetOrbitsOfTensor: Given group mut preserve the tensor of structure-constants!");
        return fail;
    fi;
    ags:=[];

    for i in asymTypes do
#        Union(List([1,2], i->  List(ags, gs->GoodSetOrbit(G,BuildGoodSet(T,gs[2][i],gs[3]),gs[1]))));

        Append(ags, Union(List([1,2], j->List(STCAsymGSReps(G,T,i), gs->GoodSetOrbit(G,BuildGoodSet(T,gs[2][j],gs[3]),gs[1])))));
#        Print(".\c");
    od;

    sgs:=[];

    for i in symTypes do
        Append(sgs, List(STCSymGSReps(G,T,i),gs->GoodSetOrbit(G, BuildGoodSet(T,gs[2][1],gs[3]), gs[1])));
#        Print(".\c");
    od;
    lgs:=Union(ags,sgs);
    return lgs;
end);


InstallGlobalFunction(STCSub,
function(G,T,symTypes,asymTypes)
    local   gss,  i,  gsa,  gs,  res,spart;


#    Print(Length(symTypes)," type(s) of symmetric good sets.\n");
#    Print(Length(asymTypes)," type(s) of antisymmetric good sets.\n");
#    Print("Computing good sets...\n");
    gs:=STCGoodSetReps(G,T,symTypes,asymTypes);
    if gs=[] then
        spart:=ShortLexSorted([ReflexiveColors(T), Difference([1..OrderOfTensor(T)], ReflexiveColors(T))]);
        spart:=FusionFromPartitionAndBaseNC(T,spart,[]);
        spart:=FusionOrbitNC(G,spart,AutomorphismGroup(T));
        res:=[spart];
    else
#        Print("\nComputing subalgebras...\n");
        res:=Concatenation(FusionOrbitsFromGoodSetOrbits(gs)); # this can be optimized by developing a new
                                                               # STCIsoSub taking into account the known
                                                               # merging type
#        Print("finished.\n");
    fi;

    return res;
end);

# returns the list of all fusion orbits (under the known color
# automorphism group of cgr1) that are color isomorphic to cgr2
InstallGlobalFunction(ColorIsomorphicFusions,
function(cgr1,cgr2)
    local   T1,  T2,  cl1,  cl2,  mergings,  symTypes,  asymTypes,
            sol,  types,  i,  sub;

    T1:=StructureConstantsOfColorGraph(cgr1);
    T2:=StructureConstantsOfColorGraph(cgr2);

    cl1:=DegreeInformationOfTensor(T1);
    cl1:=TransposedMatMutable(cl1{[1,2]});

    cl2:=DegreeInformationOfTensor(T2);
    cl2:=TransposedMatMutable(cl2{[1,2]});


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

    sub:=STCSub(ColorAutomorphismGroupOnColors(cgr1), T1,Set(symTypes),Set(asymTypes));
#    sub:=Filtered(sub, x->RankOfFusion(Representative(x))=Rank(cgr2));
    if sub=[] then
        return [];
    fi;

    # has to be filtered for color isomorphism
    sub:=Filtered(sub, x->IsColorIsomorphicColorGraph(cgr2, ColorGraphByFusion(cgr1,Representative(x))));

    return sub;
end);

InstallMethod(NormalizingPermutationOfCandidate,
        "for all good set candidates in GoodSetCandRep",
        [IsAsymGoodSetCandidate and IsSTCAsymGoodSetCandRep],
function(cand)
    return cand!.nperm;
end);

InstallMethod(NormalizingPermutationOfCandidate,
        "for all good set candidates in GoodSetCandRep",
        [IsSymGoodSetCandidate and IsSTCSymGoodSetCandRep],
function(cand)
    return cand!.nperm;
end);

InstallMethod(TensorOfCandidate,
        "for good set candidates",
        [IsAsymGoodSetCandidate and IsSTCAsymGoodSetCandRep],
function(cand)
  return cand!.tensor;
end);

InstallMethod(TensorOfCandidate,
        "for good set candidates",
        [IsSymGoodSetCandidate and IsSTCSymGoodSetCandRep],
function(cand)
  return cand!.tensor;
end);

InstallMethod(NormalizedDomainOfCandidate,
        "for good set candidates",
        [IsAsymGoodSetCandidate and IsSTCAsymGoodSetCandRep],
function(cand)
     return cand!.ndomain[cand!.currIdx];
end);

InstallMethod(NormalizedDomainOfCandidate,
        "for good set candidates",
        [IsSymGoodSetCandidate and IsSTCSymGoodSetCandRep],
function(cand)
     return cand!.ndomain[cand!.currIdx];
end);

InstallMethod(NormalizedSetOfCandidate,
        "for good set candidates",
        [IsSymGoodSetCandidate and IsSTCSymGoodSetCandRep],
function(cand)
  return Concatenation(cand!.nset);
end);

InstallMethod(NormalizedSetOfCandidate,
        "for good set candidates",
        [IsAsymGoodSetCandidate and IsSTCAsymGoodSetCandRep],
function(cand)
  return Concatenation(cand!.nset);
end);

DeclareRepresentation( "IsSubIsoLatticeRep",
        IsCocoOrbitRep,
        ["elements",     # list of all elements of the poset. The list must be
                         # ordered in a way that is compatible with the partial
                         # order relation (no element is preceeded by a greater element).
         "successors",   # on index i the list of all indices of successors of the
                         # element #i is stored
         "predecessors", # the same as successors for predecessors
         "mergings"      # if order(x,y)=true, then mergings[y] contains the fusions
                         # of elements[y] that are color isomorphic to elements[x]
         ]);



InstallGlobalFunction(SubColorIsomorphismPoset,
function(lW)
    local mergings,order,linorder,lattice;

    order:=function(y,x)
        local info;

        info:=ColorIsomorphicFusions(lW[x],lW[y]);
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

    lattice:=CocoPosetByFunctions([1..Length(lW)],order,linorder);

    lattice!.mergings:=Immutable(mergings);
    lattice!.elements:=Immutable(List(lattice!.elements, i->lW[i]));
    SetFilterObj(lattice,IsSubIsoLattice);
    SetFilterObj(lattice,IsSubIsoLatticeRep);

    return lattice;
end);
