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
#    fixed=[],              # list of colors not allowed to split during stabilization
#    variable=[],           # list of colors allowd to split during stabilization
#    classes=[],            # ordered partition of colors of the underlying CC
#                           # numbers in fixed and variable refer to indices into this list
#    instabil=FiFoNew(),
#    instabilFlags=[],
#    totest==FiFoNew(),
#    totestFlags=[],
#    colorNames,
#    numberClasses
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
    part.colorNames:=List([1..Length(part.classes)], x->[x,1]);
    part.numberClasses:=ListWithIdenticalEntries(Length(part.classes), 1);
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
    part.colorNames:=List([1..Length(part.classes)], x->[x,1]);
    part.numberClasses:=ListWithIdenticalEntries(Length(part.classes), 1);
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
    part.colorNames:=List([1..Length(part.classes)], x->[x,1]);
    part.numberClasses:=ListWithIdenticalEntries(Length(part.classes), 1);
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
    part.colorNames:=List([1..Length(part.classes)], x->[x,1]);
    part.numberClasses:=ListWithIdenticalEntries(Length(part.classes), 1);
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
    newPart.colorNames:=StructuralCopy(part.colorNames);
    newPart.numberClasses:=ShallowCopy(part.numberClasses);
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
                return fail;
            fi;
        od;
    od;

    for ii in part.variable do
        x:=WLPartitionClass(part,ii);
        colour:=Set(x, y->vec[y]);
        if Length(colour)>1 then
            classes:=List(colour, y->Filtered(x, z->vec[z]=y));
            if ForAny(classes, x->Length(x)< Length(min) or (Length(x)=Length(min) and x< min)) then
               return fail;
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
                part.colorNames[jj]:=[part.colorNames[ii][1], part.numberClasses[part.colorNames[ii][1]]+j-1];
                WLSetInstabilFlag(part,jj);
                FiFoAdd(part.instabil,jj);
                WLSetToTestFlag(part,jj);
                FiFoAdd(part.totest,jj);
            od;
            part.numberClasses[part.colorNames[ii][1]]:=part.numberClasses[part.colorNames[ii][1]]+Length(classes)-1;
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
    local u,v, i,T,part,min;

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
            if WLRepartition(T, part, u, v,min)=fail then
                return fail;
            fi;
            if u<>v and
               not IsCommutativeTensor(T) and
               (WLIsAntiSymmetricSet(T,part,v) or
                WLIsAntiSymmetricSet(T,part,u)) then
                if WLRepartition(T, part, v, u,min)=fail then
                    return fail;
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
    part.colorNames:=List([1..Length(part.classes)], x->[x,1]);
    part.numberClasses:=ListWithIdenticalEntries(Length(part.classes), 1);
    return part;
end);

InstallGlobalFunction(WLIsStablePartition,
function(T,p)
    local part;

    part:=WLBuildFixedPartition(p);
    if WLStabil(T,part)<>fail then
        return true;
    else
        return false;
    fi;
end);

InstallGlobalFunction(WLRelToMat,
function(rel,n)
    local row,arc,mat;

    row:=ListWithIdenticalEntries(n,0);
    mat:=List([1..n-1], i->ShallowCopy(row));
    Add(mat,row);
    for arc in rel do
        mat[arc[1]][arc[2]]:=1;
    od;
    MakeImmutable(mat);
    return mat;
end);

InstallGlobalFunction(WLMatRepartition,
function(part, mat) #,min)
    local ix,x,i,j,ii,jj,colour, classes,n;

    n:=Length(part.classes[1][1]);
    for ii in part.variable do
        x:=part.classes[ii][2];
        colour:=Set(x, y->mat[y[1]][y[2]]);
        if Length(colour)>1 then
            classes:=List(colour, y->Filtered(x, z->mat[z[1]][z[2]]=y));
            MakeImmutable(classes);
            part.classes[ii]:=[WLRelToMat(classes[1],n),classes[1]];
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
                Add(part.classes, [WLRelToMat(classes[j],n),classes[j]]);
                part.colorNames[jj]:=[part.colorNames[ii][1], part.numberClasses[part.colorNames[ii][1]]+j-1];
                Add(part.variable, jj);
                WLSetInstabilFlag(part,jj);
                FiFoAdd(part.instabil,jj);
                WLSetToTestFlag(part,jj);
                FiFoAdd(part.totest,jj);
            od;
            part.numberClasses[part.colorNames[ii][1]]:=part.numberClasses[part.colorNames[ii][1]]+Length(classes)-1;
        fi;
    od;
end);

InstallGlobalFunction(WLMatStabil,
function(part)
    local u,v, i,n,mat;

    u:=WLInstabilQueueRemove(part);
    while u<>false do
        for i in [1..Length(part.classes)] do
            WLToTestQueueAdd(part, i);
        od;
        v:=WLToTestQueueRemove(part);
        while v<>false do
            mat:=part.classes[u][1] * part.classes[v][1];
            WLMatRepartition(part, mat);
            if u<>v then
                mat:=part.classes[v][1] * part.classes[u][1];
                WLMatRepartition(part, mat);
            fi;
            v:=WLToTestQueueRemove(part);
        od;
        u:=WLInstabilQueueRemove(part);
    od;
    return part;
end);

InstallGlobalFunction(WLMatBuildPartition,
function(M)
    local part,l,i,colors,rels,mat,j;

    colors:=Union(M);
    rels:=List(colors, c->Filtered(Tuples([1..Length(M)],2),a->M[a[1]][a[2]]=c));
    rels:=List(rels, r->[WLRelToMat(r,Length(M)),r]);
    part:=rec();
    part.classes:=rels;
    l:=Length(part.classes);

    part.variable:=[1..Length(part.classes)];
    part.instabil:=FiFoNew();
    part.instabilFlags:=List([1..l], x->true);
    for i in [1..l] do
        FiFoAdd(part.instabil,i);
    od;
    part.totest:=FiFoNew();
    part.totestFlags:=List([1..l], x->false);
    part.colorNames:=List([1..l], x->[colors[x],1]);
    part.numberClasses:=ListWithIdenticalEntries(l, 1);

    mat:=NullMat(Length(M),Length(M));
    for i in [1..Length(M)] do
        for j in [1..Length(M)] do
            if i=j then
                mat[i][j]:=[M[i][j],[M[i][j]]];
            else
                mat[i][j]:=[M[i][j],M[j][i]];
            fi;
        od;
    od;
    WLMatRepartition(part,mat);

    return part;
end);
