#############################################################################
##
##  wlclosure.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of the Weisfeiler-Leman algorithm that works inside
##  of a given coherent configuration
##
#############################################################################

# This file contains functions for the computation of the WL-closure inside a
# given coherent configuration $W$. This is realized via a stabilization process that
# uses the structure constants of $W$.

# On November 19. 2007 this file was renamed to wl-closure.g4.
# The first step was to make the file run under GAP4.
# In particular the parts interfacing with COCOGAP had to be
# changed to call functions from coco2

# On December 5 2008 this file was renamed to wlclosure.gi
# This makes the file part of my coco2-fork

#####################################################################################
# TODO: simplify constructor to get
# input:
#  partition       --- the colour-partition for which the WL-closure is to be
#                   found
#  fixedClasses    --- a list of indices to classes in the partition that are not
#                   allowed to split
#  instabilClasses --- the list of classes of the partition that potentially will lead
#                   to a refinement
#####################################################################################

# a partition is a record:
#rec(
#    fixed=[],
#    variable=[],
#    classes=[],
#    instabil=FiFoNew(),
#    instabilFlags=[],
#    totest==FiFoNew(),
#    totestFlags=[]
#    );

InstallGlobalFunction(WLBuildAsymGoodSetPartition,
function(T, A)
    local part,rest;

    part:=rec();
    rest:= Difference(Difference([1..OrderOfTensor(T)], ReflexiveColors(T)), Union(A));
    part.classes:=[ReflexiveColors(T), A[1], A[2]];
    part.fixed:=[2];
    part.variable:=[1,3];
    part.instabil:=FiFoNew();
    FiFoAdd(part.instabil,1);
    FiFoAdd(part.instabil,2);
    FiFoAdd(part.instabil,3);
    part.instabilFlags:=[true,true,true];
    part.totest:=FiFoNew();
    part.totestFlags:=[false,false,false];
    if rest<>[] then
       Add(part.classes,rest);
       Add(part.variable,4);
       FiFoAdd(part.instabil,4);
       Add(part.totestFlags,false);
       Add(part.instabilFlags,true);
    fi;
    return part;
end);


InstallGlobalFunction(WLBuildSymGoodSetPartition,
function(T, A)
    local part,cmpl;

    part:=rec();
    part.instabil:=FiFoNew(); FiFoAdd(part.instabil,1);FiFoAdd(part.instabil,2);
    part.fixed:=[2];
    part.variable:=[1];
    part.classes:=[ReflexiveColors(T),A];
    part.instabilFlags:=[true,true];
    part.totest:=FiFoNew();
    part.totestFlags:=[false,false];

    cmpl:=Difference(Difference([1..OrderOfTensor(T)], ReflexiveColors(T)),A);
    if cmpl<>[] then
       Add(part.classes,cmpl);
       Add(part.variable,3);
       FiFoAdd(part.instabil,3);
       Add(part.instabilFlags,true);
       Add(part.totestFlags,false);
    fi;
    return part;
end);

InstallGlobalFunction(WLBuildTrivialPartition,
function(T)
    local part,nof;

    nof:=NumberOfFibres(T);
    part:=rec();
    part.classes:=[ReflexiveColors(T), Difference([1..OrderOfTensor(T)], ReflexiveColors(T))];
    part.fixed:=[];
    part.variable:=[1,2];
    part.instabilFlags:=[false,false];
    part.instabil:=FiFoNew();
    part.totest:=FiFoNew();
    part.totestFlags:=[false,false];
    return part;
end);

InstallGlobalFunction(WLBuildPartition,
function(p)
    local part,l,i;

    part:=rec();
    part.classes:=Set(p,Set);
    l:=Length(part.classes);
    part.fixed:=[];

    part.variable:=[1..Length(part.classes)];
    part.instabil:=FiFoNew();
    part.instabilFlags:=List([1..l], x->true);
    for i in [1..l] do
        FiFoAdd(part.instabil,i);
    od;
    part.totest:=FiFoNew();
    part.totestFlags:=List([1..l], x->false);
    return part;
end);

InstallGlobalFunction(WLShallowCopyStablePartition,
function(part)
    local newPart;

    newPart:=rec();
    newPart.classes:=ShallowCopy(part.classes);
    newPart.fixed:=ShallowCopy(part.fixed);
    newPart.variable:=ShallowCopy(part.variable);
    newPart.instabil:=FiFoNew();
    newPart.instabilFlags:=ShallowCopy(part.instabilFlags);
    newPart.totest:=FiFoNew();
    newPart.totestFlags:=ShallowCopy(part.totestFlags);

    return newPart;
end);

InstallGlobalFunction(WLPartitionClass,
function(part,u)
    return part.classes[u];
end);

InstallGlobalFunction(WLSetToTestFlag,
function(part,i)
    part.totestFlags[i]:=true;
end);

InstallGlobalFunction(WLClearToTestFlag,
function(part,i)
    part.totestFlags[i]:=false;
end);

InstallGlobalFunction(WLIsToTest,
function(part,i)
    return part.totestFlags[i];
end);

InstallGlobalFunction(WLToTestQueueAdd,
function(part,i)
    if not WLIsToTest(part,i) then
        WLSetToTestFlag(part,i);
        FiFoAdd(part.totest,i);
    fi;
end);

InstallGlobalFunction(WLToTestQueueRemove,
function(part)
    local i;

    i:=FiFoRemove(part.totest);
    if i = false then
        return false;
    fi;
    WLClearToTestFlag(part,i);
    return i;
end);

InstallGlobalFunction(WLSetInstabilFlag,
function(part,i)
    part.instabilFlags[i]:=true;
end);

InstallGlobalFunction(WLClearInstabilFlag,
function(part,i)
    part.instabilFlags[i]:=false;
end);

InstallGlobalFunction(WLIsInstabil,
function(part,i)
    return part.instabilFlags[i];
end);

InstallGlobalFunction(WLInstabilQueueAdd,
function(part,i)
    if not WLIsInstabil(part,i) then
        WLSetInstabilFlag(part,i);
        FiFoAdd(part.instabil, i);
    fi;
end);

InstallGlobalFunction(WLInstabilQueueRemove,
function(part)
    local i;

    i:=FiFoRemove(part.instabil);
    if i = false then
        return false;
    fi;
    WLClearInstabilFlag(part,i);
    return i;
end);


InstallGlobalFunction(WLRepartition,
function(T, part, u,v,min)
    local vec,ix,x,i,j,ii,jj,colour, classes;

    vec:=ComplexProduct(T, WLPartitionClass(part,u), WLPartitionClass(part,v));

    for ix in part.fixed do
        x:=WLPartitionClass(part,ix);
        colour:=vec[x[1]];
        for j in [2..Length(x)] do
            if vec[x[j]]<>colour then
                return false;
            fi;
        od;
    od;

    for ii in part.variable do
        x:=WLPartitionClass(part,ii);
        colour:=Set(x, y->vec[y]);
        if Length(colour)>1 then
            classes:=List(colour, y->Filtered(x, z->vec[z]=y));
            if ForAny(classes, x->Length(x)< Length(min) or (Length(x)=Length(min) and x< min)) then
               return false;
            fi;
            part.classes[ii]:=classes[1];
            if not WLIsInstabil(part,ii) then
                WLSetInstabilFlag(part,ii);
                FiFoAdd(part.instabil, ii);
            fi;
            if not WLIsToTest(part,ii) then
                WLSetToTestFlag(part,ii);
                FiFoAdd(part.totest,ii);
            fi;

            ix:=Length(part.classes);
            for j in [2..Length(classes)] do
                jj:=ix+j-1;
                Add(part.classes, classes[j]); Add(part.variable, jj);
                WLSetInstabilFlag(part,jj);
                FiFoAdd(part.instabil,jj);
                WLSetToTestFlag(part,jj);
                FiFoAdd(part.totest,jj);
            od;
        fi;
    od;
    return part;
end);

InstallGlobalFunction(WLIsAntiSymmetricSet,
function(T,part,u)
    local M;
    M:=WLPartitionClass(part,u);
    return not M[1]^Mates(T) in M;
end);

InstallGlobalFunction(WLStabil,
function(arg)
    local u,v, f,i,T,part,min;

    min:=[];
    if Length(arg)<2 or Length(arg)>3 then
       Error("WLStabil(T,part,[minsize])");
    else
       T:=arg[1];
       part:=arg[2];
       if Length(arg)=3 then
          min:=arg[3];
       fi;
    fi;
    u:=WLInstabilQueueRemove(part);
    while u<>false do
        for i in [1..Length(part.classes)] do
            WLToTestQueueAdd(part, i);
        od;
        v:=WLToTestQueueRemove(part);
        while v<>false do

            f:=WLRepartition(T, part, u, v,min);
            if f=false then
                return false;
            fi;
            if u<>v and
               not IsCommutativeTensor(T) and
               (WLIsAntiSymmetricSet(T,part,v) or
                WLIsAntiSymmetricSet(T,part,u)) then
                f:=WLRepartition(T, part, v, u,min);
                if f=false then
                    return false;
                fi;
            fi;
            v:=WLToTestQueueRemove(part);
        od;
        u:=WLInstabilQueueRemove(part);
    od;
    return part;
end);


InstallGlobalFunction(WLBuildFixedPartition,
function(p)
    local part,l,i;

    part:=rec();
    part.classes:=Set(List(p,Set));
    l:=Length(part.classes);
    part.fixed:=[1..l];
    part.variable:=[];
    part.instabil:=FiFoNew();
    part.instabilFlags:=List([1..l], x->true);
    for i in [1..l] do
        FiFoAdd(part.instabil,i);
    od;
    part.totest:=FiFoNew();
    part.totestFlags:=List([1..l], x->false);
    return part;
end);

InstallGlobalFunction(WLIsStablePartition,
function(T,p)
    local part;

    part:=WLBuildFixedPartition(p);
    if WLStabil(T,part)<>false then
        return true;
    else
        return false;
    fi;
end);
