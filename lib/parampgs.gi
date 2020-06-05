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

#      -  cls[i] is a set of colors
#      -  x[i] elements have to be chosen from cls[i], for every i
#         as we are constructing symmetric good sets, when cls[i][j] is choosen,
#         then also cls[i][j]^Mates(tensor) needs to be choosen. However, this mate
#         is neither an element of cls[i], nor is it counted in x[i]
InstallMethod(EmptySymPartialGoodSetWithParams,
        "for blocked tensors of structure constants, two lists and a positive int",
        [IsTensor and IsTensorOfCC and IsBlockedTensorRep, IsList, IsList, IsPosInt, IsInt],
function(tensor,x,cls,k,lbd)
    local  mat, vec, perm, blocks, startBlock, finishBlock, rclr, clr, 
           nof, imap, a, sclr, aclr, b, bclr, map, i, j, idx, nsupply, 
           currIdx, dom, obj, domain, set, task, done;
    
    mat:=List(tensor!.blocks, a->List(tensor!.blocks, Length));
    vec:=List(mat,Sum);
    # perm:=();
    perm:=SortingPerm(vec);
    blocks:=Permuted(List(tensor!.blocks, x->Permuted(x,perm)),perm);
    startBlock:=List([1..Order(tensor)], i->StartBlock(tensor,i)^perm);
    finishBlock:=List([1..Order(tensor)], i->FinishBlock(tensor,i)^perm);
    
    rclr:=ReflexiveColors(tensor);
    clr:=Difference([1..OrderOfTensor(tensor)], rclr);
    nof:=Length(rclr);
    
    imap:=[];
    
    for a in [1..nof] do
        sclr:=Intersection(Filtered(blocks[a][a], x->x^Mates(tensor)=x),clr);
        aclr:=Filtered(blocks[a][a], x->x<x^Mates(tensor));
        imap[a]:=List(sclr, x->[x]);
        Append(imap[a], List(aclr, x->[x,x^Mates(tensor)]));
        SortBy(imap[a], x->-Sum(List(x,i->-OutValencies(tensor)[i])));
    od;

    for a in [1..nof] do
        for b in [a+1..nof] do
            bclr:=ShallowCopy(blocks[a][b]);
            SortBy(bclr, i->-OutValencies(tensor)[i]);
            Append(imap[a], List(bclr, x->Set([x,x^Mates(tensor)])));
        od;
    od;
    imap:=Concatenation(imap);
    
    map:=[];
    for i in [1..Length(imap)] do
        for j in imap[i] do
            map[j]:=i;
        od;
    od;
    
    # remove empty classes and sort colors by blocks
    idx:=Filtered([1..Length(cls)], i->x[i]<>0);
    x:=x{idx};
    cls:=cls{idx};
    SortParallel(cls,x,function(c1,c2) return Set([startBlock[c1[1]],finishBlock[c1[1]]])<Set([startBlock[c2[1]],finishBlock[c2[1]]]);end);
    nsupply:=List(cls, x->Set(x, i->map[i]));
    
    SortParallel(nsupply,x, function(a,b) return Minimum(a)<Minimum(b);end);
    
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
    
    
    return Objectify(NewType(GoodSetsFamily(tensor), IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep), obj);
end);

InstallMethod(IsCompatiblePoint,
        "for symmetric partial good sets with params in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep, IsPosInt],
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
              lbd:=cand!.lbd
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

InstallMethod(IsCompletePartialGoodSet,
     "for symmetric partial good sets in SymPGSWithParamsBlkRep",
    [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
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
    COCOPrint(".\c");
    
    return BuildGoodSet(cand!.tensor, set, part.classes);
end);

InstallMethod(DomainOfPartialGoodSet,
        "for partial good sets in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
function(cand)
    return cand!.domain;
end);

InstallMethod(TensorOfPartialGoodSet,
        "for partial good sets in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
function(cand)
    return cand!.tensor;
end);

InstallMethod(IMapOfPartialGoodSet,
        "for partial good sets in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
function(cand)
    return cand!.imap;
end);

InstallMethod(IsEmptyPartialGoodSet,
        "for partial good sets in SymPGSWithParamsBlkRep",
        [IsSymPartialGoodSet and IsSymPGSWithParamsBlkRep],
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
    COCOPrint("!\c");
    res:=[];
    for sol in types do
        cand:=EmptySymPartialGoodSetWithParams(tensor,sol,cls,k,lbd);
        iter:=IteratorOfPartialGoodSetOrbits(AutomorphismGroup(tensor),cand);
        Append(res, AllGoodSetOrbits(iter));
        COCOPrint("#\c");
    od;

    return res;
end);

