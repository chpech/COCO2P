InstallGlobalFunction(MatrixAndBoundsSym,
function(tensor)
    local  clr, nof, mat, c, row, pos,cls;

    clr:=Difference([1..Order(tensor)],ReflexiveColors(tensor));
    clr:=Filtered(clr, x->x<=x^Mates(tensor));
    nof:=Length(ReflexiveColors(tensor));
    mat:=[];
    cls:=[];
    
    for c in clr do
        row:=ListWithIdenticalEntries(nof,0);
        row[StartBlock(tensor,c)]:=OutValencies(tensor)[c];
        if c^Mates(tensor)<>c then
            row[StartBlock(tensor,c^Mates(tensor))]:=row[StartBlock(tensor,c^Mates(tensor))] + OutValencies(tensor)[c^Mates(tensor)];
        fi;
        pos:=PositionSorted(mat,row);
        if not IsBound(mat[pos]) or mat[pos]<>row then
            Add(mat,row,pos);
            Add(cls,[c],pos);
        else
            AddSet(cls[pos],c);
        fi;
    od;
    return [mat,List(cls,Length),cls];
end);

InstallGlobalFunction(MatrixAndBoundsAsym,
function(tensor)
    local  clr, nof, mat, c, row, pos,cls;

    clr:=Difference([1..Order(tensor)],ReflexiveColors(tensor));
    clr:=Filtered(clr, x->x<>x^Mates(tensor));
    nof:=Length(ReflexiveColors(tensor));
    mat:=[];
    cls:=[];
    
    for c in clr do
        row:=ListWithIdenticalEntries(nof,0);
        row[StartBlock(tensor,c)]:=OutValencies(tensor)[c];
        pos:=PositionSorted(mat,row);
        if not IsBound(mat[pos]) or mat[pos]<>row then
            Add(mat,row,pos);
            Add(cls,[c],pos);
        else
            AddSet(cls[pos],c);
        fi;
    od;
    return [mat,List(cls,Length),cls];
end);


DeclareRepresentation("IsSymPGSWithParamsBlkRep",
                      IsAttributeStoringRep,
                      [ 
                          "tensor",
                          "perm",
                          "blocks",
                          "startBlock",
                          "finishBlock",
                          "map",
                          "imap",
                          "domain",
                          "nsupply",
                          "set",
                          "task",
                          "done",
                          "currIdx",
                          "square",
                          "lbd",
                          "fullrows",
                          "degreelist"
                      ]);

DeclareRepresentation("IsSymPGSWithParamsRep",
                      IsAttributeStoringRep,
                      [ 
                          "tensor",
                          "domain",
                          "map",
                          "imap",
                          "nsupply",
                          "set",
                          "task",
                          "done",
                          "currIdx",
                          "k",
                          "lbd",
                          "square",
                          "degree",
                          "maxlbd"
                      ]);

DeclareRepresentation("IsAsymPGSWithParamsRep",
                      IsAttributeStoringRep,
                      [ 
                          "tensor",
                          "domain",# a list of classes of points each is a subset of the 
                                   # corresponding class of nsupply, it encodes the still 
                                   # avaylable points from nsupply (mutable) 
                          "map",   # every actual color is mapped to a local index (point) 
                                   # this allows reordering and identification 
                                   # of colors as fits (immutable)
                          "imap",  # the inverse map of map (immutable)
                          "nsupply", # a list of classes of points
                                     # the number of points to be chosen from each class 
                                     # is given in task (immutable)
                          "insupply", # the mapping that maps each point to the index of 
                                      # its class in nsupply (immutable)
                          "set",    # the set of colors already chosen by the algorithm (mutable)
                          "task",   # for each class of nsupply this holds the number of
                                    # points to be chosen from this class (immutable)
                          "done",   # the number of points already chosen from the class 
                                    # of nsupply with index currIdx (mutable)
                          "currIdx", # the index to the class in nsupply currently active (mutable)
                          "k",       # the goal valencu of set (immutable and irrelevant 
                                     # for the algorithm)
                          "lbd",     # the goal arc-valency of set (immutable and relevant 
                                     # for the algorithm)
                          "square",  # the coefficients vector of set^2
                          "degree",  # the actual valency of set
                          "maxlbd",  # the maximal arc-valency of set
                      ]);



#      -  cls[i] is a set of colors
#      -  x[i] elements have to be chosen from cls[i], for every i
#         as we are constructing symmetric good sets, when cls[i][j] is choosen,
#         then also cls[i][j]^Mates(tensor) needs to be choosen. However, this mate
#         is neither an element of cls[i], nor is it counted in x[i]
InstallMethod(EmptySymPartialGoodSetWithParams,
        "for blocked tensors of structure constants, two lists and a positive int",
        [IsTensor and IsTensorOfCC and IsBlockedTensorRep, IsList, IsList, IsPosInt, IsInt],
function(tensor,x,cls,k,lbd)
    local  vec, perm, blocks, startBlock, finishBlock, rclr, clr, 
           nof, imap, a, sclr, aclr, b, bclr, map, i, j, idx, nsupply, 
           currIdx, dom, obj, domain, set, task, done, blkidx,xcls,d,c,cblk;
    
    #mat:=List(tensor!.blocks, a->List(tensor!.blocks, Length));
    #vec:=List(mat,Sum);
    
#    vec:=List([1..Length(t!.blocks)], i->Length(t!.blocks[i][i]));
#    perm:=SortingPerm(vec);
#    perm:=SortingPerm(vec);
    perm:=();
    blocks:=Permuted(List(tensor!.blocks, x->Permuted(x,perm)),perm);
    startBlock:=List([1..Order(tensor)], i->StartBlock(tensor,i)^perm);
    finishBlock:=List([1..Order(tensor)], i->FinishBlock(tensor,i)^perm);
    
    idx:=Filtered([1..Length(cls)], i->x[i]<>0);
    x:=x{idx};
    cls:=cls{idx};
    SortParallel(cls,x,function(c1,c2) return SortedList([startBlock[c1[1]],finishBlock[c1[1]]])<SortedList([startBlock[c2[1]],finishBlock[c2[1]]]);end);
    
    
#    rclr:=ReflexiveColors(tensor);
#    clr:=Difference([1..OrderOfTensor(tensor)], rclr);
    nof:=NumberOfFibres(tensor);
#    blk:=List(cls, x->Set([startBlock[x[1]],finishBlock[x[1]]]));
    # blkidx:=List(Set(blk), x->Filtered([1..Length(cls)], i->blk[i]=x));
    # xcls:=List(cls, x->Union(List(x, y->[x,x^Mates(tensor)])))
    # xcls:=List([1..Length(blk)], i->Concatenation(cls{blkidx[i]}));
    # xcls
    # List([1..Length(blk)], i->,Difference
    # clr:=Concatenation(cls);
    # imap:=List(clr, x->Set([x,x^Mates(tensor)]));
    
    
    imap:=List([1..nof], i->List([1..nof],j->[]));
    for c in cls do
        for d in c do
            blkidx:=SortedList([startBlock[d],finishBlock[d]]);
            Add(imap[blkidx[1]][blkidx[2]],Set([d,d^Mates(tensor)]));
        od;
    od;
    
    for a in [1..nof] do
        for b in [a..nof] do
            cblk:=Difference(blocks[a][b], Union(imap[a][b]));
            if a=b then
                cblk:=Filtered(cblk, x->x<=x^Mates(tensor));
            fi;
            Append(imap[a][b], List(cblk, x->Set([x,x^Mates(tensor)])));
        od;
    od;
    
    
    # for a in [1..nof] do
    #     sclr:=Intersection(Filtered(blocks[a][a], x->x^Mates(tensor)=x),clr);
    #     aclr:=Filtered(blocks[a][a], x->x<x^Mates(tensor));
    #     imap[a]:=List(sclr, x->[x]);
    #     Append(imap[a], List(aclr, x->[x,x^Mates(tensor)]));
    #     SortBy(imap[a], x->-Sum(List(x,i->-OutValencies(tensor)[i])));
    # od;

    # for a in [1..nof] do
    #     for b in [a+1..nof] do
    #         bclr:=ShallowCopy(blocks[a][b]);
    #         SortBy(bclr, i->-OutValencies(tensor)[i]);
    #         Append(imap[a], List(bclr, x->Set([x,x^Mates(tensor)])));
    #     od;
    # od;
    
    imap:=Concatenation(Concatenation(imap));
    
    map:=[];
    for i in [1..Length(imap)] do
        for j in imap[i] do
            map[j]:=i;
        od;
    od;
    
    # remove empty classes and sort colors by blocks
    # idx:=Filtered([1..Length(cls)], i->x[i]<>0);
    # x:=x{idx};
    # cls:=cls{idx};
    # SortParallel(cls,x,function(c1,c2) return Set([startBlock[c1[1]],finishBlock[c1[1]]])<Set([startBlock[c2[1]],finishBlock[c2[1]]]);end);
    nsupply:=List(cls, x->Set(x, i->map[i]));
    
#    SortParallel(nsupply,x, function(a,b) return Minimum(a)<Minimum(b);end);
    
    currIdx:=1;
    if nsupply=[] then
        dom:=[];
    else
        dom:=nsupply[currIdx];
    fi;
    
    obj:=rec( tensor:=tensor,
              blocks:=blocks,
              startBlock:=startBlock,
              finishBlock:=finishBlock,
              perm:=perm,
              map:=map,
              imap:=imap,
              domain:=dom,
              nsupply:=nsupply,
              set:=[],
              blockingmat:=List([1..nof], a->List([1..nof], b->[])),
              task:=x,
              done:=ListWithIdenticalEntries(Length(x),0),
              currIdx:=currIdx,
              k:=k,
              lbd:=lbd,
              square:=ListWithIdenticalEntries(OrderOfTensor(tensor),0),
              fullrows:=[],
              degreelist:=ListWithIdenticalEntries(nof,0),
              maxlbd:=0,
              ridx:=[]
            );
   # Error("brk");
    
    
    return Objectify(NewType(GoodSetsFamily(tensor), IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep), obj);
end);

InstallMethod(EmptySymPartialGoodSetWithParams,
        "for dense tensors of structure constants, two lists and a positive int",
        [IsTensor and IsTensorOfCC and IsTensorRep, IsList, IsList, IsPosInt, IsInt],
function(tensor,x,cls,k,lbd)
    local  idx, nsupply, currIdx, dom, obj,map,imap,c,d,i,j;
    
    
    idx:=Filtered([1..Length(cls)], i->x[i]<>0);
    x:=x{idx};
    
    imap:=[];
    
    cls:=cls{idx};
    for c in cls do
        for d in c do
            Add(imap, Set([d,d^Mates(tensor)]));
        od;
    od;
    map:=[];
    for i in [1..Length(imap)] do
        for j in imap[i] do
            map[j]:=i;
        od;
    od;

    
    nsupply:=List(cls, x->Set(x, i->map[i]));

    currIdx:=1;
    if nsupply=[] then
        dom:=[];
    else
        dom:=nsupply[currIdx];
    fi;
    
    obj:=rec( tensor:=tensor,
              domain:=dom,
              map:=map,
              imap:=imap,
              nsupply:=nsupply,
              set:=[],
              task:=x,
              done:=ListWithIdenticalEntries(Length(x),0),
              currIdx:=currIdx,
              k:=k,
              lbd:=lbd,
              square:=ListWithIdenticalEntries(OrderOfTensor(tensor),0),
              degree:=0,
              maxlbd:=0
            );
   # Error("brk");
    
    
    return Objectify(NewType(GoodSetsFamily(tensor), IsSymPartialGoodSet and IsSymPGSWithParamsRep), obj);
end);

InstallMethod(EmptyAsymPartialGoodSetWithParams,
        "for tensors of structure constants, two lists, a positive int and an int",
        [IsTensor and IsTensorOfCC and IsTensorRep, IsList, IsList, IsPosInt, IsInt],
function(tensor,x,cls,k,lbd)
    local  idx, nsupply, currIdx, dom, obj,map,imap,c,d,i,j,insupply;
    
    
    idx:=Filtered([1..Length(cls)], i->x[i]<>0);
    x:=x{idx};
    
    imap:=[];
    
    cls:=cls{idx};
    for c in cls do
        for d in c do
            Add(imap, d);
        od;
    od;
    
    map:=[];
    for i in [1..Length(imap)] do
        map[imap[i]]:=i;
    od;
    MakeImmutable(map);
    imap:=List(imap, x->[x]);
    
    MakeImmutable(imap);
        
    nsupply:=List(cls, x->Set(x, i->map[i]));
    MakeImmutable(nsupply);
    
    insupply:=[];
    for i in [1..Length(nsupply)] do
        for j in nsupply[i] do
            insupply[j]:=i;
        od;
    od;
    MakeImmutable(insupply);
    
    
    currIdx:=1;
    if nsupply=[] then
        dom:=[];
    else
        dom:=List(nsupply, ShallowCopy);
    fi;
    
    obj:=rec( tensor:=tensor,
              domain:=dom,
              map:=map,
              imap:=imap,
              nsupply:=nsupply,
              insupply:=insupply,
              set:=[],
              task:=x,
              done:=ListWithIdenticalEntries(Length(x),0),
              currIdx:=currIdx,
              k:=k,
              lbd:=lbd,
              square:=ListWithIdenticalEntries(OrderOfTensor(tensor),0),
              degree:=0,
              maxlbd:=0
            );    
    
    return Objectify(NewType(GoodSetsFamily(tensor), IsAsymPartialGoodSet and IsAsymPGSWithParamsRep), obj);
end);

InstallMethod(IsCompatiblePoint,
        "for symmetric partial good sets with params in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep, IsPosInt],
function(cand, i)
    return true;
end);

InstallMethod(IsCompatiblePoint,
        "for symmetric partial good sets with params in SymPGSWithParamsRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsRep, IsPosInt],
function(cand, i)
    return true;
end);

InstallMethod(IsCompatiblePoint,
        "for asymmetric partial good sets with params in AsymPGSWithParamsRep",
        [IsAsymPartialGoodSet and IsAsymPGSWithParamsRep, IsPosInt],
function(cand, i)
    return true;
end);

InstallMethod(ExtendedPartialGoodSet,
        "for symmetric partial good sets with params in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep, IsPosInt],
function(cand,pt)
    local  t, obj, color, icolor, sb, fb, sd, 
           sbinfr, fbinfr,  sq, ent, 
           blkIdx, bm, block, ba, bb, bc, bbl, b, j;
    
    t:=cand!.tensor;
    
    obj:=rec(
              tensor:=cand!.tensor,
              blocks:=cand!.blocks,
              startBlock:=cand!.startBlock,
              finishBlock:=cand!.finishBlock,
              perm:=cand!.perm,
              map:=cand!.map,
              imap:=cand!.imap,
              nsupply:=cand!.nsupply,
              task:=cand!.task,
              k:=cand!.k,
              lbd:=cand!.lbd,
             );
    color:=cand!.imap[pt][1];
    icolor:=color^Mates(t);
    sb:=cand!.startBlock[color];
    fb:=cand!.finishBlock[color];
    
    if fb<sb then
        color:=cand!.imap[pt][2];
        icolor:=cand!.imap[pt][1];
        sb:=cand!.startBlock[color];
        fb:=cand!.finishBlock[color];
    fi;
    
    sd:=OutValencies(t);
    obj.degreelist:=ShallowCopy(cand!.degreelist);
    
    
    obj.degreelist[sb]:=obj.degreelist[sb]+sd[color];
    if color<>icolor then
        obj.degreelist[fb]:=obj.degreelist[fb]+sd[icolor];
    fi;
    
    obj.fullrows:=ShallowCopy(cand!.fullrows);
    
    sbinfr:=obj.degreelist[sb]=obj.k;
    if  sbinfr then
        AddSet(obj.fullrows,sb);
    fi;
    if sb <> fb then
        fbinfr:=obj.degreelist[fb]=obj.k;
        if  fbinfr then
            AddSet(obj.fullrows,fb);
        fi;
    else
        fbinfr:=sbinfr;
    fi;
    
    if cand!.done[cand!.currIdx]+1=cand!.task[cand!.currIdx] then
        obj.currIdx:=cand!.currIdx+1;
        if obj.currIdx <= Length(cand!.task) then
            obj.domain:=cand!.nsupply[obj.currIdx];
        else
            obj.domain:=[];
        fi;
    else
        obj.domain:=Filtered(cand!.domain, x->x>pt);
        obj.currIdx:=cand!.currIdx;
    fi;
    
    obj.done:=ShallowCopy(cand!.done);
    obj.done[cand!.currIdx]:=obj.done[cand!.currIdx]+1;
#    obj.set:=ShallowCopy(cand!.set);
#    obj.set[cand!.currIdx]:=Union(obj.set[cand!.currIdx],cand!.imap[pt]);
    obj.set:=Union(cand!.set, [color,icolor]);
    obj.ridx:=Union(cand!.ridx,[sb,fb]);

    obj.blockingmat:=ShallowCopy(cand!.blockingmat);
    obj.blockingmat[sb]:=ShallowCopy(obj.blockingmat[sb]);
    obj.blockingmat[sb][fb]:=ShallowCopy(obj.blockingmat[sb][fb]);
    AddSet(obj.blockingmat[sb][fb],color);
    if color<>icolor then
        if fb<>sb then
            obj.blockingmat[fb]:=ShallowCopy(obj.blockingmat[fb]);
            obj.blockingmat[fb][sb]:=ShallowCopy(obj.blockingmat[fb][sb]);
        fi;
        AddSet(obj.blockingmat[fb][sb],icolor);
    fi;

    
    obj.square:=ShallowCopy(cand!.square);
    sq:=obj.square;
    ent:=t!.entries;
    blkIdx:=t!.blkIdx;
    
    
    bm:=obj.blockingmat;
    obj.maxlbd:=cand!.maxlbd;
    
    if color<>icolor then
        if sb=fb then
            block:=bm[sb][fb]; # c c,c* c*
            ba:=sb/obj.perm;
            bb:=sb/obj.perm;
            bc:=sb/obj.perm;
            bbl:=cand!.blocks[sb][sb];
            sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[color]][blkIdx[color]];
            sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[icolor]][blkIdx[icolor]];
            
            if block<>[] then
                obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{block}));
            fi;
            if obj.maxlbd> obj.lbd then
                return fail;
            fi;
        fi;
        block:=bm[fb][fb];   # c* c
        ba:=fb/obj.perm;
        bb:=fb/obj.perm;
        bc:=sb/obj.perm;
        bbl:=cand!.blocks[fb][fb];
        sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[icolor]][blkIdx[color]];
        
        if block<>[] then
            obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{block}));
        fi;
        if obj.maxlbd> obj.lbd then
            return fail;
        fi;
        for b in cand!.ridx do        # c* A*
            if fb<=b then
                block:=bm[fb][b];
                for j in cand!.blockingmat[sb][b] do
                    ba:=fb/obj.perm;
                    bb:=b/obj.perm;
                    bc:=sb/obj.perm;
                    bbl:=cand!.blocks[fb][b];
                    sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[icolor]][blkIdx[j]];
                od;
                if block<>[] then
                    obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{block}));
                fi;
                if fb<>sb and b<>sb and b<>fb and block<>[] then    # if block(=bm[fb][b]) is complete
                    if fbinfr and b in obj.fullrows then
                        if ForAny(block, x->sq[x]<>obj.lbd) then
#                            return fail;
                        fi;
                    fi;
                fi;
                if obj.maxlbd> obj.lbd then
                    return fail;
                fi;
            fi;
            
            if b<=fb then
                block:=bm[b][fb];   # A c
                for j in cand!.blockingmat[b][sb] do
                    ba:=b/obj.perm;
                    bb:=fb/obj.perm;
                    bc:=sb/obj.perm;
                    bbl:=cand!.blocks[b][fb];
                    sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[j]][blkIdx[color]];
                od;
                if block<>[] then
                    obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{block}));
                fi;
                if fb<>sb and b<>sb and block<>[] then # if block(=bm[b][fb]) is complete
                    if  fbinfr and b in obj.fullrows  then
                        if ForAny(block, x->sq[x]<> obj.lbd) then
                            return fail;
                        fi;
                    fi;
                fi;
                if obj.maxlbd> obj.lbd then
                    return fail;
                fi;
            fi;
        od;
    fi;
    block:=bm[sb][sb];      # c c*
    ba:=sb/obj.perm;
    bb:=sb/obj.perm;
    bc:=fb/obj.perm;
    bbl:=cand!.blocks[sb][sb];
    sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[color]][blkIdx[icolor]];

    if block<>[] then
        obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{block}));
    fi;
    if obj.maxlbd> obj.lbd then
        return fail;
    fi;
        
    for b in cand!.ridx do      # c A*
        if sb<=b then
            block:=bm[sb][b];
            for j in cand!.blockingmat[fb][b] do
                ba:=sb/obj.perm;
                bb:=b/obj.perm;
                bc:=fb/obj.perm;
                bbl:=cand!.blocks[sb][b];
                sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[color]][blkIdx[j]];
            od;
            if block<>[] then
                obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{block}));
            fi;
            if b<>sb  and block<>[] then   # if block(=bm[sb][b]) is complete
                if sbinfr and b in obj.fullrows then
                    if ForAny(block, x->sq[x] <> obj.lbd) then
                        return fail;
                    fi;
                fi;
            fi;
            if obj.maxlbd> obj.lbd then
                return fail;
            fi;
        fi;
        if b<=sb then
            block:=bm[b][sb]; # A c*
            for j in cand!.blockingmat[b][fb] do
                ba:=b/obj.perm;
                bb:=sb/obj.perm;
                bc:=fb/obj.perm;
                bbl:=cand!.blocks[b][sb];
                sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[j]][blkIdx[icolor]];
            od;
            if block<>[] then
                obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{block}));
            fi;
            if  block<>[] then # block (=bm[b][sb] is complete  
                if sbinfr and b in obj.fullrows then 
                    if ForAny(block, x->sq[x] <> obj.lbd) then
                        return fail;
                    fi;
                fi;
            fi;
            if obj.maxlbd> obj.lbd then
                return fail;
            fi;
        fi;
    od;
    
    if sbinfr and ForAny(obj.blockingmat[sb][sb], x->sq[x]<>obj.lbd) then
        return fail;
    fi;
    if sb<>fb and fbinfr and ForAny(obj.blockingmat[fb][fb], x->sq[x]<>obj.lbd) then
        return fail;
    fi;
    if sb<>fb and sbinfr and fbinfr and ForAny(obj.blockingmat[sb][fb], x->sq[x]<>obj.lbd) then
        return fail;
    fi;
    
    
    return Objectify(NewType(GoodSetsFamily(cand!.tensor), IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep), obj);
end);

InstallMethod(ExtendedPartialGoodSet,
        "for symmetric partial good sets with params in SymPGSWithParamsRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsRep, IsPosInt],
function(cand,pt)
    local  t, obj, color, icolor, sd,  sq, ent, j;
    
    t:=cand!.tensor;
    
    obj:=rec(
              tensor:=cand!.tensor,
              map:=cand!.map,
              imap:=cand!.imap,
              nsupply:=cand!.nsupply,
              task:=cand!.task,
              k:=cand!.k,
              lbd:=cand!.lbd,
             );
    color:=cand!.imap[pt][1];
    icolor:=color^Mates(t);
    
    sd:=OutValencies(t);
    obj.degree:=cand!.degree;
    
    
    obj.degree:=obj.degree+sd[color];
    if color<>icolor then
        obj.degree:=obj.degree+sd[icolor];
    fi;
    
    
    
    if cand!.done[cand!.currIdx]+1=cand!.task[cand!.currIdx] then
        obj.currIdx:=cand!.currIdx+1;
        if obj.currIdx <= Length(cand!.task) then
            obj.domain:=cand!.nsupply[obj.currIdx];
        else
            obj.domain:=[];
        fi;
    else
        obj.domain:=Filtered(cand!.domain, x->x>pt);
        obj.currIdx:=cand!.currIdx;
    fi;
    
    obj.done:=ShallowCopy(cand!.done);
    obj.done[cand!.currIdx]:=obj.done[cand!.currIdx]+1;
    obj.set:=Union(cand!.set, [color,icolor]);

    sq:=ShallowCopy(cand!.square);
    ent:=t!.entries;
    
    
    obj.maxlbd:=cand!.maxlbd;
    
    sq:=sq+ent[color][color];       # c c
    if color <> icolor then
        sq:=sq+ent[icolor][icolor]; # c* c* 
        sq:=sq+ent[color][icolor];  # c c*
        sq:=sq+ent[icolor][color];  # c* c
    fi;
    
    obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{obj.set}));
    if obj.maxlbd> obj.lbd then
        return fail;
    fi;
    
    for j in cand!.set do        
        sq:=sq+ent[j][color];   # A c
        sq:=sq+ent[color][j];   # c A
        if color <> icolor then
            sq:=sq+ent[j][icolor]; # A c*
            sq:=sq+ent[icolor][j]; # c* A
        fi;
        
        
        obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{obj.set}));
        if obj.maxlbd > obj.lbd then
            return fail;
        fi;
    od;
    obj.square:=sq;
    
    
    return Objectify(NewType(GoodSetsFamily(cand!.tensor), IsSymPartialGoodSet and IsSymPGSWithParamsRep), obj);
end);

InstallMethod(ExtendedPartialGoodSet,
        "for asymmetric partial good sets with params in AsymPGSWithParamsRep",
        [IsAsymPartialGoodSet and IsAsymPGSWithParamsRep, IsPosInt],
function(cand,pt)
    local  t, obj, color, icolor, sd,  sq, ent, j, ipt;
    
    t:=cand!.tensor;
    
    obj:=rec(
              tensor:=cand!.tensor,
              map:=cand!.map,
              imap:=cand!.imap,
              nsupply:=cand!.nsupply,
              insupply:=cand!.insupply,
              task:=cand!.task,
              k:=cand!.k,
              lbd:=cand!.lbd,
             );
    color:=cand!.imap[pt][1];
    icolor:=color^Mates(t);
    ipt:=cand!.map[icolor];
    
    
    sd:=OutValencies(t);
    obj.degree:=cand!.degree;
    
    
    obj.degree:=obj.degree+sd[color];
    
    obj.domain:=List(cand!.domain, ShallowCopy);
    
    if cand!.done[cand!.currIdx]+1=cand!.task[cand!.currIdx] then
        obj.currIdx:=cand!.currIdx+1;
    else
        obj.domain[cand!.currIdx]:=Filtered(cand!.domain[cand!.currIdx], x->x>pt);
        obj.currIdx:=cand!.currIdx;
        if obj.insupply[ipt]>=obj.currIdx then
            RemoveSet(obj.domain[obj.insupply[ipt]],ipt);
        fi;
    fi;
    
    obj.done:=ShallowCopy(cand!.done);
    obj.done[cand!.currIdx]:=obj.done[cand!.currIdx]+1;
    obj.set:=Union(cand!.set, [color]);

    sq:=ShallowCopy(cand!.square);
    ent:=t!.entries;
    
    
    obj.maxlbd:=cand!.maxlbd;
    
    sq:=sq+ent[color][color];       # c c
    
    obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{obj.set}));
    if obj.maxlbd> obj.lbd then
        return fail;
    fi;
    
    for j in cand!.set do        
        sq:=sq+ent[j][color];   # A c
        sq:=sq+ent[color][j];   # c A
        
        
        obj.maxlbd:=Maximum(obj.maxlbd, Maximum(sq{obj.set}));
        if obj.maxlbd > obj.lbd then
            return fail;
        fi;
    od;
    obj.square:=sq;
    
    
    return Objectify(NewType(GoodSetsFamily(cand!.tensor), IsAsymPartialGoodSet and IsAsymPGSWithParamsRep), obj);
end);

InstallMethod(IsCompletePartialGoodSet,
     "for symmetric partial good sets in SymPGSWithParamsBlkRep",
    [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
function(cand)
    
    return cand!.currIdx>Length(cand!.task);
end);

InstallMethod(IsCompletePartialGoodSet,
     "for symmetric partial good sets in SymPGSWithParamsRep",
    [IsSymPartialGoodSet and IsSymPGSWithParamsRep],
function(cand)
    
    return cand!.currIdx>Length(cand!.task);
end);

InstallMethod(IsCompletePartialGoodSet,
     "for asymmetric partial good sets in AsymPGSWithParamsRep",
    [IsAsymPartialGoodSet and IsAsymPGSWithParamsRep],
function(cand)
    return cand!.currIdx>Length(cand!.task);
end);

InstallMethod(GoodSetFromPartialGoodSet,
     "for symmetric partial good sets in SymPGSWithParamsBlkRep",
    [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
function(cand)
    local   set,  i,  res,  part;
    
    set:=cand!.set;

    part:=WLBuildSymGoodSetPartition(cand!.tensor,set);
    part:=WLStabil(cand!.tensor,part);
    if part=fail then
        return fail;
    fi;
    
    return BuildGoodSet(cand!.tensor, set, part.classes);
end);

InstallMethod(GoodSetFromPartialGoodSet,
     "for symmetric partial good sets in SymPGSWithParamsRep",
    [IsSymPartialGoodSet and IsSymPGSWithParamsRep],
function(cand)
    local   set,  i,  res,  part;
    
    set:=cand!.set;

    part:=WLBuildSymGoodSetPartition(cand!.tensor,set);
    part:=WLStabil(cand!.tensor,part);
    if part=fail then
        return fail;
    fi;
    
    return BuildGoodSet(cand!.tensor, set, part.classes);
end);

InstallMethod(GoodSetFromPartialGoodSet,
     "for asymmetric partial good sets in AsymPGSWithParamsRep",
    [IsAsymPartialGoodSet and IsAsymPGSWithParamsRep],
function(cand)
    local  T, set, gs, part;
    
    T:=cand!.tensor;
    set:=cand!.set;

    gs:=[set,OnSets(set,Mates(T))];
    
    part:=WLBuildAsymGoodSetPartition(T,gs);
    part:=WLStabil(T,part);
    if part=fail then
        return fail;
    fi;
    
    return BuildGoodSet(T, set, part.classes);
end);

InstallMethod(DomainOfPartialGoodSet,
        "for partial good sets in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
function(cand)
    return cand!.domain;
end);

InstallMethod(DomainOfPartialGoodSet,
        "for partial good sets in SymPGSWithParamsRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsRep],
function(cand)
    return cand!.domain;
end);

InstallMethod(DomainOfPartialGoodSet,
        "for partial good sets in AsymPGSWithParamsRep",
        [IsAsymPartialGoodSet and IsAsymPGSWithParamsRep],
function(cand)
    if cand!.currIdx> Length(cand!.domain) then
        return [];
    fi;
    
    return cand!.domain[cand!.currIdx];
end);

InstallMethod(TensorOfPartialGoodSet,
        "for partial good sets in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
function(cand)
    return cand!.tensor;
end);

InstallMethod(TensorOfPartialGoodSet,
        "for partial good sets in SymPGSWithParamsRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsRep],
function(cand)
    return cand!.tensor;
end);

InstallMethod(TensorOfPartialGoodSet,
        "for partial good sets in AsymPGSWithParamsRep",
        [IsAsymPartialGoodSet and IsAsymPGSWithParamsRep],
function(cand)
    return cand!.tensor;
end);

InstallMethod(IMapOfPartialGoodSet,
        "for partial good sets in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
function(cand)
    return cand!.imap;
end);

InstallMethod(IMapOfPartialGoodSet,
        "for partial good sets in SymPGSWithParamsRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsRep],
function(cand)
    return cand!.imap;
end);

InstallMethod(IMapOfPartialGoodSet,
        "for partial good sets in AsymPGSWithParamsRep",
        [IsAsymPartialGoodSet and IsAsymPGSWithParamsRep],
function(cand)
    return cand!.imap;
end);

InstallMethod(IsEmptyPartialGoodSet,
        "for partial good sets in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
function(cand)
    return cand!.set=[];
end);

InstallMethod(IsEmptyPartialGoodSet,
        "for partial good sets in SymPGSWithParamsRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsRep],
function(cand)
    return cand!.set=[];
end);

InstallMethod(IsEmptyPartialGoodSet,
        "for partial good sets in AsymPGSWithParamsRep",
        [IsAsymPartialGoodSet and IsAsymPGSWithParamsRep],
function(cand)
    return cand!.set=[];
end);

InstallMethod(IsExtendiblePartialGoodSet,
        "for partial good sets in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
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

InstallMethod(IsExtendiblePartialGoodSet,
        "for partial good sets in SymPGSWithParamsRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsRep],
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

InstallMethod(IsExtendiblePartialGoodSet,
        "for partial good sets in AsymPGSWithParamsRep",
        [IsAsymPartialGoodSet and IsAsymPGSWithParamsRep],
function(cand)
    if cand!.currIdx>Length(cand!.task) then
        return false;
    fi;
    if cand!.done[cand!.currIdx]+Length(cand!.domain[cand!.currIdx])<cand!.task[cand!.currIdx] then
        return false;
    fi;
    if ForAll([cand!.currIdx..Length(cand!.task)], i->cand!.done[i]=cand!.task[i]) then
        return false;
    fi;
    
    return true;
end);

InstallMethod(HomogeneousSymGoodSetOrbitsWithParameters,
        "for structure constants tensors",
        [IsTensor and IsTensorOfCC, IsPosInt, IsInt],
function(tensor,k,lbd)
    local  mb, mat, bounds, cls, types, res, sol, cand, iter;
    
    mb:=MatrixAndBoundsSym(tensor);
    mat:=mb[1];
    bounds:=mb[2];
    cls:=mb[3];
    types:=BoundedSolutionsOfSLDE(mat,bounds,k);
    Info(InfoCOCO,1,"!");
    res:=[];
    for sol in types do
        cand:=EmptySymPartialGoodSetWithParams(tensor,sol,cls,k,lbd);
        iter:=IteratorOfPartialGoodSetOrbits(AutomorphismGroup(tensor),cand);
        Append(res, AllGoodSetOrbits(iter));
        Info(InfoCOCO,2,"#");
    od;

    return res;
end);

InstallMethod(HomogeneousAsymGoodSetOrbitsWithParameters,
        "for structure constants tensors",
        [IsTensor and IsTensorOfCC, IsPosInt, IsInt],
function(tensor,k,lbd)
    local  mb, mat, bounds, cls, types, res, sol, cand, iter;
    
    mb:=MatrixAndBoundsAsym(tensor);
    mat:=mb[1];
    bounds:=mb[2];
    cls:=mb[3];
    if mat=[] then
        return [];
    fi;
    
    types:=BoundedSolutionsOfSLDE(mat,bounds,k);
    Info(InfoCOCO,1,"!");
    res:=[];
    for sol in types do
        cand:=EmptyAsymPartialGoodSetWithParams(tensor,sol,cls,k,lbd);
        iter:=IteratorOfPartialGoodSetOrbits(AutomorphismGroup(tensor),cand);
        Append(res, AllGoodSetOrbits(iter));
        Info(InfoCOCO,2,"#");
    od;

    return res;
end);
