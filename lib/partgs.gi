#############################################################################
##
##  partgs.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of partial good sets  
##
#############################################################################


DeclareRepresentation("IsPartialGoodSetRep",
        IsAttributeStoringRep,
        [ "tensor",
          "map",
          "imap",
          "domain",
          "set",
          "maxlength",
          "square"
          ]);

BindGlobal("nonext",false);

#
# methods for all partial good sets
#
InstallMethod(IsExtendiblePartialGoodSet,
    "for partial good sets in PartialGoodSetRep",
    [IsPartialGoodSet and IsPartialGoodSetRep],
function(cand)
   if cand!.domain=[] then
      return false;
   fi;

   if Length(cand!.set)>=cand!.maxlength then
      return false;
   fi;

   return true;
end);

InstallMethod(DomainOfPartialGoodSet,
        "for partial good sets in PartialGoodSetRep",
        [IsPartialGoodSet and IsPartialGoodSetRep],
function(cand)
    return cand!.domain;
end);

InstallMethod(IsCompatiblePoint,
        "for partial good sets in PartialGoodSetRep and positive integers",
        [IsPartialGoodSet and IsPartialGoodSetRep, IsPosInt],
function(cand, i)
    return true;
end);


InstallMethod(TensorOfPartialGoodSet,
        "for partial good sets in PartialGoodSetRep",
        [IsPartialGoodSet and IsPartialGoodSetRep],
function(cand)
    return cand!.tensor;
end);

InstallMethod(IMapOfPartialGoodSet,
        "for partial good sets in PartialGoodSetRep",
        [IsPartialGoodSet and IsPartialGoodSetRep],
function(cand)
    return cand!.imap;
end);

InstallMethod(IsEmptyPartialGoodSet,
        "for partial good sets in PartialGoodSetRep",
        [IsPartialGoodSet and IsPartialGoodSetRep],
function(cand)
    return cand!.set=[];
end);

InstallMethod( ViewString,
        "for partial good sets in PartialGoodSetRep",
        [IsPartialGoodSet and IsPartialGoodSetRep],
function(pgs)
    local t,s,res;
    
    t:=pgs!.tensor;
    s:=pgs!.set;

    res:="<";
    if s<>[] and not s[1]^Mates(t) in s then
        Append(res,"antisymmetric ");
    else
        Append(res,"symmetric ");
    fi;

    return Concatenation(res,"partial good set ", String(s), ">");
end);

InstallMethod(IsCompletePartialGoodSet,
    "for partial good sets in PartialGoodSetRep",
    [IsPartialGoodSet and IsPartialGoodSetRep],
function(pgs)
    local set,sqr;
    
    set:=pgs!.set;
    
    if set = [] then
        return false;
    fi;
    if Length(pgs!.set)>pgs!.maxlength then
      return false;
   fi;

    sqr:=pgs!.square;
    if Length(set)>1 and ForAny([2..Length(set)], i->sqr[set[1]]<>sqr[set[i]]) then
        return false;
    fi;
    return true;
end);

#
# symmetric partial good sets in homogeneous tensors
#

InstallMethod(GoodSetFromPartialGoodSet,
    "for symmetric partial good sets in PartialGoodSetRep",
    [IsSymPartialGoodSet and IsPartialGoodSetRep],
function(cand)
    local  part;
       
    part:=WLBuildSymGoodSetPartition(cand!.tensor,cand!.set);
    part:=WLStabil(cand!.tensor,part);
    if part= fail then
        return fail;
    fi;
    
    return BuildGoodSet(cand!.tensor, cand!.set, part.classes);
    
end);

InstallMethod(ExtendedPartialGoodSet,
    "for symmetric partial good sets in PartialGoodSetRep",
    [IsSymPartialGoodSet and IsPartialGoodSetRep, IsPosInt],
function(cand,pt)
   local ndom,obj,ent,sq,mates,i;
   
   ent:=cand!.tensor!.entries;
   mates:=cand!.imap[pt];
   sq:=ShallowCopy(cand!.square);
   for i in cand!.set do
       sq:=sq+ent[i][mates[1]];
       sq:=sq+ent[mates[1]][i];
   od;
   sq:=sq+ent[mates[1]][mates[1]];
   if Length(mates)=2 then
       for i in cand!.set do
           sq:=sq+ent[i][mates[2]];
           sq:=sq+ent[mates[2]][i];
       od;
       sq:=sq+ent[mates[1]][mates[2]];
       sq:=sq+ent[mates[2]][mates[1]];
       sq:=sq+ent[mates[2]][mates[2]];
   fi;
   
   ndom:=Filtered(cand!.domain, x->x>pt);

   obj:=rec(
            tensor:=cand!.tensor,
            map:=cand!.map,
            imap:=cand!.imap,
            domain:=ndom,
            set:=Union(cand!.set,cand!.imap[pt]),
            maxlength:=cand!.maxlength,
            square:=sq);
   
   return Objectify(NewType(GoodSetsFamily(cand!.tensor), IsSymPartialGoodSet and IsPartialGoodSetRep), obj);
end);


InstallMethod(EmptySymPartialGoodSet,
        "for homogeneous tensors of structure constants",
        [IsTensor and IsTensorOfCC and IsHomogeneousTensor],
function(tensor)
    local aaut,rclr,clr,sclr,aclr,imap,map, i, j,act,cand;
   
    rclr:=ReflexiveColors(tensor);
    clr:=Difference([1..OrderOfTensor(tensor)], rclr);
    sclr:=Filtered(clr, x->x^Mates(tensor)=x);
    aclr:=Filtered(clr, x->x<x^Mates(tensor));
    imap:=[];
 
    Append(imap, List(sclr, x->[x]));
    Append(imap,List(aclr, x->[x,x^Mates(tensor)]));
    map:=[];
    for i in [1..Length(imap)] do
        for j in imap[i] do
            map[j]:=i;
        od;
    od;
    
    cand:=rec(tensor:=tensor,
              map:=map,
              imap:=imap,
              domain:=[1..Length(imap)],
              set:=[],               
              maxlength:=Int((OrderOfTensor(tensor)-1)/2),
              square:=ListWithIdenticalEntries(0,OrderOfTensor(tensor))
              );
   
   return Objectify(NewType(GoodSetsFamily(tensor), IsSymPartialGoodSet and IsPartialGoodSetRep), cand);
end);


#
# Asymmetric candidates in homogeneous tensors
#
    
InstallMethod(GoodSetFromPartialGoodSet,
    "for asymmetric partial good sets in PartialGoodSetRep",
    [IsAsymPartialGoodSet and IsPartialGoodSetRep],
function(cand)
    local T,set,gs,part;
    
    T:=cand!.tensor;
    set:=cand!.set;
    
    gs:=[set, OnSets(set, Mates(T))];
    part:=WLBuildAsymGoodSetPartition(T,gs);
    part:=WLStabil(T,part);
    if part = fail then
        return fail;
    fi;
    
    return BuildGoodSet(T, set,part.classes);
end);

InstallMethod(ExtendedPartialGoodSet,
    "for asymmetric partial good sets in PartialGoodSetRep",
    [IsAsymPartialGoodSet and IsPartialGoodSetRep, IsPosInt],
function(cand,pt)
    local t,clr,ent,ipt,ndom,obj,sq,i;
    
    t:=cand!.tensor;
    clr:=cand!.imap[pt][1];
    ipt:=cand!.map[cand!.imap[pt][1]^Mates(t)];
    ent:=t!.entries;
    
    sq:=ShallowCopy(cand!.square);
    for i in cand!.set do
        sq:=sq+ent[i][clr];
        sq:=sq+ent[clr][i];
    od;
    sq:=sq+ent[clr][clr];
    
    ndom:=Filtered(cand!.domain, x->x>pt and x<>ipt);
   
    obj:=rec(
             tensor:=cand!.tensor,
             map:=cand!.map,
             imap:=cand!.imap,
             domain:=ndom,
             set:=Union(cand!.set,cand!.imap[pt]),
             maxlength:=cand!.maxlength,
             square:=sq);
   
   return Objectify(NewType(GoodSetsFamily(cand!.tensor), IsAsymPartialGoodSet and IsPartialGoodSetRep), obj);
end);

InstallMethod(EmptyAsymPartialGoodSet,
        "for homogeneous tensors of structure constants",
        [IsTensor and IsTensorOfCC and IsHomogeneousTensor],
function(tensor)
    local imap,map,i,grp,act,cand;
    
    imap:=Filtered([1..OrderOfTensor(tensor)], x->x^Mates(tensor)<>x);
    map:=[];
    for i in [1..Length(imap)] do
        map[imap[i]]:=i;
    od;

    imap:=List(imap, x->[x]);
      
    cand:=rec(tensor:=tensor,
              map:=map,
              imap:=imap,
              domain:=[1..Length(imap)],
              set:=[],
              maxlength:=Int((OrderOfTensor(tensor)-1)/2),
              square:=ListWithIdenticalEntries(0,OrderOfTensor(tensor))
              );
    
    return Objectify(NewType(GoodSetsFamily(tensor), IsAsymPartialGoodSet and IsPartialGoodSetRep), cand);
end);


##############################################################################
#
# homogeneous partial asymmetric godd set for inhomogeneous CCs
#
##############################################################################

DeclareRepresentation("IsAsymPartialGoodSetBlkRep",
        IsPartialGoodSetRep,
        [ "tensor",
          "blocks",
          "perm",
          "startBlock",
          "finishBlock",
          "map",
          "imap",
          "domain",
          "currentRow",
          "set",
          "maxlength",
          "blockingmat",
          "rowdegs",
          "coldegs",
          "rmaxdeg",
          "cmaxdeg",
          "domrowdegs",
          "domcoldegs",
          "ridx",
          "cidx",
          "square",
          "fullrows",
          "kIsForced",
          "k",
          "lbdIsForced",
          "lbd"
          ]);


InstallMethod(IsCompletePartialGoodSet,
    "for asymmetric partial good sets in AsymPartialGoodSetBlkRep",
    [IsAsymPartialGoodSet and IsAsymPartialGoodSetBlkRep],
function(cand)
    local a,b,block;
    
    if cand!.set=[] then
        return false;
    fi;
    if Length(cand!.set)>cand!.maxlength then
      return false;
   fi;

    if cand!.kIsForced then 
        return Length(cand!.fullrows)=Length(cand!.blocks);
    else
        if cand!.rmaxdeg<>cand!.cmaxdeg then
            return false;
        fi;
        if ForAny([1..Length(cand!.blocks)], b->cand!.rowdegs[b]<>cand!.rmaxdeg) then
            return false;
        fi;
        if ForAny([1..Length(cand!.blocks)], b->cand!.coldegs[b]<>cand!.rmaxdeg) then
            return false;
        fi;
        
        for b in [1..Length(cand!.blocks)] do
            for a in [1..b] do 
                block:=cand!.blockingmat[a][b];
                if ForAny(block, x->cand!.square[x]<>cand!.maxlbd) then
                    return false;
                fi;
            od;
        od;
    fi;
    
    
    return true;
end);

InstallMethod(IsCompatiblePoint,
    "for asymmetric partial good sets in AsymPartialGoodSetBlkRep",
    [IsAsymPartialGoodSet and IsAsymPartialGoodSetBlkRep, IsPosInt],
function(cand,i)
    local  t, clr, sb;
    
   # return true;
    
    
    t:=cand!.tensor;
    clr:=cand!.imap[i][1];
   
    sb:=cand!.startBlock[clr];
       
    if sb-1>cand!.currentRow then
        return false;
    fi;
    return true;
end);

InstallMethod(ExtendedPartialGoodSet,
    "for asymmetric partial good sets in AsymPartialGoodSetBlkRep",
    [IsAsymPartialGoodSet and IsAsymPartialGoodSetBlkRep, IsPosInt],
function(cand,pt)
    local t,bm,npgs,color,sb,fb,sd,i,j,k,kmts,a,b,block,md,sq,icolor,ksb,kfb,sbinfr,ent,blkIdx,ba,bb,bc,bbl;

    t:=cand!.tensor;
    
    npgs:=rec(
              tensor:=cand!.tensor,
              blocks:=cand!.blocks,
              perm:=cand!.perm,
              startBlock:=cand!.startBlock,
              finishBlock:=cand!.finishBlock,
              map:=cand!.map,
              imap:=cand!.imap,
              maxlength:=cand!.maxlength
              );
    
    color:=cand!.imap[pt][1];
    sb:=cand!.startBlock[color];
    fb:=cand!.finishBlock[color];
    
    npgs.currentRow:=sb;
    
    npgs.fullrows:=ShallowCopy(cand!.fullrows);
    npgs.kIsForced:=cand!.kIsForced;
    npgs.k:=cand!.k;
    npgs.lbdIsForced:=cand!.lbdIsForced;
    npgs.lbd:=cand!.lbd;
    
    if not npgs.kIsForced then
        if sb>1 then
            npgs.kIsForced:=true;
            npgs.k:=cand!.rowdegs[1];
            
            if npgs.k<cand!.rmaxdeg or npgs.k<cand!.cmaxdeg then
                return nonext;
            fi;
            if ForAny([2..sb-1], x->cand!.rowdegs[x]<>npgs.k) then
                return nonext;
            fi;
            npgs.fullrows:=[1..sb-1];
            for i in [1..Length(npgs.fullrows)] do
                b:=npgs.fullrows[i];
                for j in [1..i] do
                    a:=npgs.fullrows[j];
                    block:=cand!.blockingmat[a][b];
                    if block<>[] then
                        npgs.lbdIsForced:=true;
                        npgs.lbd:=cand!.square[block[1]];
                        if npgs.lbd<cand!.maxlbd then
                            return nonext;
                        fi;
                        break;
                    fi;
                od;
                if npgs.lbdIsForced then
                    break;
                fi;
            od;
            if npgs.lbdIsForced then
                for i in [i..Length(npgs.fullrows)] do
                    b:=npgs.fullrows[i];
                    for j in [1..i] do
                        a:=npgs.fullrows[j];
                        if ForAny(cand!.blockingmat[a][b], x->cand!.square[x]<>npgs.lbd) then
                            return nonext;
                        fi;
                    od;
                od;
            fi;
        fi;
    fi;
    
    if npgs.lbdIsForced and cand!.square[color]>npgs.lbd then
        return fail;
    fi;
    npgs.set:=Union(cand!.set, [color]);
   
    npgs.ridx:=Union(cand!.ridx,[sb]);
    npgs.cidx:=Union(cand!.cidx,[fb]);
    
    sd:=OutValencies(t);
    
    npgs.blockingmat:=ShallowCopy(cand!.blockingmat);
    npgs.blockingmat[sb]:=ShallowCopy(npgs.blockingmat[sb]);
    npgs.blockingmat[sb][fb]:=ShallowCopy(npgs.blockingmat[sb][fb]);
    AddSet(npgs.blockingmat[sb][fb],color);   
   
    npgs.rowdegs:=ShallowCopy(cand!.rowdegs);
    npgs.coldegs:=ShallowCopy(cand!.coldegs);

    npgs.rowdegs[sb]:=npgs.rowdegs[sb]+sd[color];
    npgs.rmaxdeg:=Maximum(npgs.rowdegs[sb], cand!.rmaxdeg);
    icolor:=color^Mates(t);
    npgs.coldegs[fb]:=npgs.coldegs[fb]+sd[icolor];
    npgs.cmaxdeg:=Maximum(npgs.coldegs[fb], cand!.cmaxdeg);    
    md:=Maximum(npgs.rmaxdeg, npgs.cmaxdeg);
    
    if npgs.kIsForced and md>npgs.k then
        return fail;
    fi;
    
    sbinfr:=npgs.kIsForced and npgs.rowdegs[sb]=npgs.k;
    if sbinfr then
        AddSet(npgs.fullrows,sb);
    fi;
    
    npgs.domain:=[];
    npgs.domrowdegs:=ShallowCopy(cand!.domrowdegs);
    npgs.domcoldegs:=ShallowCopy(cand!.domcoldegs);
    for k in cand!.domain do
#        k:=cand!.domain[j];
        kmts:=[cand!.imap[k][1],cand!.imap[k][1]^Mates(t)];
        ksb:=cand!.startBlock[kmts[1]];
        kfb:=cand!.finishBlock[kmts[1]];
        if k<=pt  
           or kmts[1]=color^Mates(t) 
           or ksb in npgs.fullrows  
           or npgs.kIsForced and (sd[kmts[1]]+npgs.rowdegs[ksb]>npgs.k 
                   or sd[kmts[2]]+npgs.coldegs[kfb]>npgs.k) 
           then
            npgs.domrowdegs[ksb]:=npgs.domrowdegs[ksb]-sd[kmts[1]];
            npgs.domcoldegs[kfb]:=npgs.domcoldegs[kfb]-sd[kmts[2]];
            if npgs.domrowdegs[ksb]+npgs.rowdegs[ksb]<md or npgs.domcoldegs[kfb]+npgs.coldegs[kfb]<md then
                return fail;
            fi;
        else 
            Add(npgs.domain,k);
        fi;
    od;
    
    npgs.square:=ShallowCopy(cand!.square);
    sq:=npgs.square;
    bm:=npgs.blockingmat;
    npgs.maxlbd:=cand!.maxlbd;
    ent:=t!.entries;
    blkIdx:=t!.blkIdx;
    
    
    
    block:=bm[sb][sb];      # c c*
    ba:=sb/npgs.perm;
    bb:=sb/npgs.perm;
    bc:=fb/npgs.perm;
    bbl:=cand!.blocks[sb][sb];

    sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[color]][blkIdx[icolor]];
    
    if block<>[] then
        npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
    fi;
    if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
        return fail;
    fi;

    for b in cand!.ridx do      # c A*
        if true or sb<=b then
            block:=bm[sb][b];
            for j in cand!.blockingmat[b][fb] do
                ba:=sb/npgs.perm;
                bb:=b/npgs.perm;
                bc:=fb/npgs.perm;
                bbl:=cand!.blocks[sb][b];
                sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[color]][blkIdx[j^Mates(t)]];
            od;
            if block<>[] then
                npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
            fi;
            if b<>sb  and block<>[] then   # if block(=bm[sb][b]) is complete
                if sbinfr and b in npgs.fullrows then
                    if not npgs.lbdIsForced then
                        npgs.lbdIsForced:=true;
                        npgs.lbd:=sq[block[1]];
                        if npgs.lbd<npgs.maxlbd then
                            return fail;
                        fi;
                    fi;
                    if ForAny(block, x->sq[x] <> npgs.lbd) then
                        return fail;
                    fi;
                fi;
            fi;
            if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
                return fail;
            fi;
        fi;
        if b<=sb then
            block:=bm[b][sb]; # A c*
            for j in cand!.blockingmat[b][fb] do
                ba:=b/npgs.perm;
                bb:=sb/npgs.perm;
                bc:=fb/npgs.perm;
                bbl:=cand!.blocks[b][sb];
                sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[j]][blkIdx[icolor]];
            od;
            if block<>[] then
                npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
            fi;
            if  block<>[] then # block (=bm[b][sb] is complete  
                if sbinfr and b in npgs.fullrows then 
                    if not npgs.lbdIsForced then 
                        npgs.lbdIsForced:=true;
                        npgs.lbd:=sq[block[1]];
                        if npgs.lbd<npgs.maxlbd then
                            return fail;
                        fi;
                    fi;
                    if ForAny(block, x->sq[x] <> npgs.lbd) then
                        return fail;
                    fi;
                fi;
            fi;
            if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
                return fail;
            fi;
        fi;
    od;
    
    # if npgs.lbdIsForced then
    #     for i in [1..Length(npgs.fullrows)] do
    #         a:=npgs.fullrows[i];
    #         for j in [i..Length(npgs.fullrows)] do
    #             b:=npgs.fullrows[j];
    #             block:=npgs.blockingmat[a][b];
    #             if block <>[] then
    #                 if Length(Set(npgs.square{block}))>1 then
    #                     Error("Error 1");
    #                 fi;
    #                 if npgs.square[block[1]]<>npgs.lbd then
    #                     Error("Error 2");
    #                 fi;
    #             fi;
    #         od;
    #     od;
    # fi;

     Assert(1,sq=ComplexProduct(t,npgs.set,OnSets(npgs.set,Mates(t))));
    
    
    Objectify(NewType(GoodSetsFamily(t), IsAsymPartialGoodSet and IsAsymPartialGoodSetBlkRep), npgs);
    return npgs;
end);


InstallMethod(EmptyAsymPartialGoodSet,
        "for blocked tensors of structure constants",
        [IsTensor and IsTensorOfCC and IsBlockedTensorRep],
function(tensor)
    local mat,vec,perm,blocks,startBlock,finishBlock,nof,imap,a,b,map,i,clr,cand,sb,fb,domrowdegs,domcoldegs;
    
    
    mat:=List(tensor!.blocks, a->List(tensor!.blocks, Length));
    vec:=List(mat,Sum);
    # perm:=();
    perm:=SortingPerm(vec);
    blocks:=tensor!.blocks;
    blocks:=Permuted(List(tensor!.blocks, x->Permuted(x,perm)),perm);
    startBlock:=List([1..Order(tensor)], i->StartBlock(tensor,i)^perm);
    finishBlock:=List([1..Order(tensor)], i->FinishBlock(tensor,i)^perm);
    
    nof:=Length(blocks);
    imap:=[];
    
    for a in [1..nof] do
        for b in [1..nof] do 
            if a=b then
                clr:=Filtered(blocks[a][a], x->x^Mates(tensor)<>x);
                SortBy(clr, i->-OutValencies(tensor)[i]);
                Append(imap, clr);
            else
                clr:=ShallowCopy(blocks[a][b]);
                SortBy(clr, i->-OutValencies(tensor)[i]);
                Append(imap, clr);
            fi;
        od;
    od;
  
    map:=[];
    for i in [1..Length(imap)] do
        map[imap[i]]:=i;
    od;
    clr:=Set(imap);
    imap:=List(imap, x->[x]);    
    
    domrowdegs:=ListWithIdenticalEntries(nof,0);
    domcoldegs:=ListWithIdenticalEntries(nof,0);
    for i in clr do
        sb:=startBlock[i];
        fb:=finishBlock[i];
        domrowdegs[sb]:=domrowdegs[sb]+OutValencies(tensor)[i];
        domcoldegs[fb]:=domcoldegs[fb]+OutValencies(tensor)[i^Mates(tensor)];
    od;
    
    
    cand:=rec(tensor:=tensor,
              blocks:=blocks,
              perm:=perm,
              startBlock:=startBlock,
              finishBlock:=finishBlock,
              map:=map,
              imap:=imap,
              domain:=[1..Length(imap)],
              currentRow:=0,
              set:=[],
              maxlength:=Int((OrderOfTensor(tensor)-nof)/2),
              blockingmat:=List([1..nof], a->List([1..nof], b->[])),
              rowdegs:=ListWithIdenticalEntries(nof,0),
              coldegs:=ListWithIdenticalEntries(nof,0),
              rmaxdeg:=0,
              cmaxdeg:=0,
              maxlbd:=0,
              domrowdegs:=domrowdegs,
              domcoldegs:=domcoldegs,
              ridx:=[],
              cidx:=[],
              square:=ListWithIdenticalEntries(Order(tensor),0),
              fullrows:=[],
              kIsForced:=false,
              k:=0,
              lbdIsForced:=false,
              lbd:=0);
    return Objectify(NewType(GoodSetsFamily(tensor), IsAsymPartialGoodSet and IsAsymPartialGoodSetBlkRep), cand);
end);

##############################################################################
#
# homogeneous symmetric godd set candidates for inhomogeneous CCs
#
##############################################################################

DeclareRepresentation("IsSymPartialGoodSetBlkRep",
        IsPartialGoodSetRep,
        [ "tensor",
          "blocks",
          "perm",
          "startBlock",
          "finishBlock",
          "map",
          "imap",
          "domain",
          "currentRow",
          "set",
          "maxlength",
          "blockingmat",
          "degreelist",
          "maxdeg",
          "maxlbd",
          "domdegreelist",
          "ridx",
          "square",
          "fullrows",
          "kIsForced",
          "k",
          "lbdIsForced",
          "lbd"
          ]);

InstallMethod(IsCompletePartialGoodSet,
    "for symmetric partial good sets in SymPartialGoodSetBlkRep",
    [IsSymPartialGoodSet and IsSymPartialGoodSetBlkRep],
function(cand)
    local a,b,block;
    
    if cand!.set=[] then
        return false;
    fi;
    
    if Length(cand!.set)>cand!.maxlength then
        return false;
    fi;
    
    if cand!.kIsForced then
        return Length(cand!.fullrows)=Length(cand!.blocks);
    else
        if ForAny([1..Length(cand!.blocks)], b->cand!.degreelist[b]<>cand!.maxdeg) then
            return false;
        fi;
    
        for b in [1..Length(cand!.blocks)] do
            for a in [1..b] do 
                block:=cand!.blockingmat[a][b];
                if ForAny(block, x->cand!.square[x]<>cand!.maxlbd) then
                    return false;
                fi;
            od;
        od;
    fi;
    
    return true;
end);

InstallMethod(IsCompatiblePoint,
    "for symmetric partial good sets in SymPartialGoodSetBlk",
    [IsSymPartialGoodSet and IsSymPartialGoodSetBlkRep, IsPosInt],
function(cand,i)
    local  t, mates, sb, fb,  pos;
    
    t:=cand!.tensor;
    mates:=cand!.imap[i];
   
    sb:=cand!.startBlock[mates[1]];
    fb:=cand!.finishBlock[mates[1]];
    pos:=Minimum([sb,fb]);  # this is the row in which i resides
    if pos<=2 then
        return true;
    fi;
    
    if pos=cand!.currentRow then
        return true;
    fi;
    
    if not sb in cand!.fullrows and not fb in cand!.fullrows then
        return true;
    fi;
    
    
    if IsSubset(cand!.fullrows, [cand!.currentRow..pos-1]) then
#        Assert(1,IsSubset(Union(cand!.fullrows,[cand!.currentRow]), [1..pos-1]));
        
        return true;
    fi;
    
    
    return false;
end);

testflag:=false;
stt:=List([1..24],x->0);


InstallMethod(ExtendedPartialGoodSet,
    "for symmetric partial good sets in SymPartialGoodSetBlk",
    [IsSymPartialGoodSet and IsSymPartialGoodSetBlkRep, IsPosInt],
function(cand,pt)
    local t,npgs,color,icolor,sb,fb,i,b,j,a,block,sd,sbinfr,fbinfr,sq,bm,k,kmts,
          ksb,kfb,ncand,ent,blkIdx,ba,bb,bc,bbl;                
    
    
    t:=cand!.tensor;
    
    npgs:=rec(
              tensor:=cand!.tensor,
              blocks:=cand!.blocks,
              perm:=cand!.perm,
              startBlock:=cand!.startBlock,
              finishBlock:=cand!.finishBlock,
              map:=cand!.map,
              imap:=cand!.imap,
              maxlength:=cand!.maxlength
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
        
    npgs.fullrows:=ShallowCopy(cand!.fullrows);
    npgs.kIsForced:=cand!.kIsForced;
    npgs.k:=cand!.k;
    npgs.lbdIsForced:=cand!.lbdIsForced;
    npgs.lbd:=cand!.lbd;
    if not cand!.kIsForced then
        if sb>1 then
            npgs.kIsForced:=true;
            npgs.k:=cand!.degreelist[1];
            if npgs.k<cand!.maxdeg then
                stt[1]:=stt[1]+1;
                return nonext;
            fi;
            if ForAny([2..sb-1], x->cand!.degreelist[x]<>npgs.k) then
                stt[2]:=stt[2]+1;
                return nonext;
            fi;
            
            npgs.fullrows:=Filtered([1..Length(cand!.blocks)], x->cand!.degreelist[x]=npgs.k);
            for i in [1..Length(npgs.fullrows)] do
                a:=npgs.fullrows[i];
                for j in [i..Length(npgs.fullrows)] do
                    b:=npgs.fullrows[j];
                    block:=cand!.blockingmat[a][b];
                    if block<>[] then
                        npgs.lbdIsForced:=true;
                        npgs.lbd:=cand!.square[block[1]];
                        if npgs.lbd<cand!.maxlbd then
                            stt[3]:=stt[3]+1;
                            return nonext;
                        fi;
                        break;
                    fi;
                od;
                if npgs.lbdIsForced then
                    break;
                fi;
            od;
            if npgs.lbdIsForced then
                for i in [i..Length(npgs.fullrows)] do
                    a:=npgs.fullrows[i];
                    for j in [i..Length(npgs.fullrows)] do
                        b:=npgs.fullrows[j];
                        if ForAny(cand!.blockingmat[a][b], x->cand!.square[x]<>npgs.lbd) then
                            stt[4]:=stt[4]+1;
                            return nonext;
                        fi;
                    od;
                od;
            fi;
        fi;
    # else
    #     if ForAny([cand!.currentRow..sb-1], x->cand!.degreelist[x]<>cand!.k) then
    #         Error("test");
    #         return fail;
    #     fi;

    fi;
        
    npgs.currentRow:=sb;
    
    # if cand!.set = [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,33,34,35,36,37,49,50] and pt = 16 then
    #     Error("brk1");
    # fi;
    
    
    
    if npgs.lbdIsForced and (cand!.square[color]>npgs.lbd or (color<>icolor and cand!.square[icolor]>npgs.lbd) )then
        stt[5]:=stt[5]+1;
        return fail;
    fi;
    
    # starting from here we actually define the set of npgs
    npgs.set:=Union(cand!.set, [color,icolor]);
    npgs.ridx:=Union(cand!.ridx,[sb,fb]);
    
    sd:=OutValencies(t);
    
    npgs.blockingmat:=ShallowCopy(cand!.blockingmat);
    npgs.blockingmat[sb]:=ShallowCopy(npgs.blockingmat[sb]);
    npgs.blockingmat[sb][fb]:=ShallowCopy(npgs.blockingmat[sb][fb]);
    AddSet(npgs.blockingmat[sb][fb],color);
    
    npgs.degreelist:=ShallowCopy(cand!.degreelist);
    npgs.degreelist[sb]:=npgs.degreelist[sb]+sd[color];
    npgs.maxdeg:=Maximum(cand!.maxdeg, npgs.degreelist[sb]);
    
    if color<>icolor then
        if fb<>sb then
            npgs.blockingmat[fb]:=ShallowCopy(npgs.blockingmat[fb]);
            npgs.blockingmat[fb][sb]:=ShallowCopy(npgs.blockingmat[fb][sb]);
        fi;
        AddSet(npgs.blockingmat[fb][sb],icolor);
        npgs.degreelist[fb]:=npgs.degreelist[fb]+sd[icolor];
        npgs.maxdeg:=Maximum(npgs.maxdeg, npgs.degreelist[fb]);
    fi;
    if npgs.kIsForced and npgs.maxdeg>npgs.k then
        stt[6]:=stt[6]+1;
        return fail;
    fi;
    
    sbinfr:=npgs.kIsForced and npgs.degreelist[sb]=npgs.k;
    if sbinfr then
        AddSet(npgs.fullrows,sb);
    fi;
    
    if fb<>sb then
        fbinfr:=npgs.kIsForced and npgs.degreelist[fb]=npgs.k;
        if fbinfr then
            AddSet(npgs.fullrows,fb);
        fi;
    else
        fbinfr:=sbinfr;
    fi;
    
    npgs.domain:=[];
    npgs.domdegreelist:=ShallowCopy(cand!.domdegreelist);
    for j in [1..Length(cand!.domain)] do
        k:=cand!.domain[j];
        kmts:=cand!.imap[k];
        ksb:=cand!.startBlock[kmts[1]];
        kfb:=cand!.finishBlock[kmts[1]];
        if k<=pt 
           or ksb in npgs.fullrows
           or kfb in npgs.fullrows
           or npgs.kIsForced and (sd[kmts[1]]+npgs.degreelist[ksb]>npgs.k 
                   or  (Length(kmts)=2 and sd[kmts[2]]+npgs.degreelist[kfb]>npgs.k))
#           or npgs.lbdIsForced and (sq[kmts[1]]>npgs.lbd 
#                   or (Length(kmts)=2 and sq[kmts[2]]>npgs.lbd))
           then
            npgs.domdegreelist[ksb]:=npgs.domdegreelist[ksb]-sd[kmts[1]];
            if npgs.domdegreelist[ksb]+npgs.degreelist[ksb]<npgs.maxdeg then
                stt[7]:=stt[7]+1;
                return fail;
            fi;
            if Length(kmts)=2 then
                npgs.domdegreelist[kfb]:=npgs.domdegreelist[kfb]-sd[kmts[2]];
                if npgs.domdegreelist[kfb]+npgs.degreelist[kfb]<npgs.maxdeg then
                    stt[8]:=stt[8]+1;
                    return fail;
                fi;
            fi;
        else
            Add(npgs.domain,k);
        fi;
    od;    

    npgs.square:=ShallowCopy(cand!.square);
    sq:=npgs.square;
    ent:=t!.entries;
    blkIdx:=t!.blkIdx;
    
    
    bm:=npgs.blockingmat;
    npgs.maxlbd:=cand!.maxlbd;
    
    if color<>icolor then
        if sb=fb then
            block:=bm[sb][fb]; # c c,c* c*
            ba:=sb/npgs.perm;
            bb:=sb/npgs.perm;
            bc:=sb/npgs.perm;
            bbl:=cand!.blocks[sb][sb];
            sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[color]][blkIdx[color]];
            sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[icolor]][blkIdx[icolor]];
            
            if block<>[] then
                npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
            fi;
            if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
                stt[9]:=stt[9]+1;
                return fail;
            fi;
        fi;
        block:=bm[fb][fb];   # c* c
        ba:=fb/npgs.perm;
        bb:=fb/npgs.perm;
        bc:=sb/npgs.perm;
        bbl:=cand!.blocks[fb][fb];
        sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[icolor]][blkIdx[color]];
        
        if block<>[] then
            npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
        fi;
        if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
            stt[10]:=stt[10]+1;
            return fail;
        fi;
        for b in cand!.ridx do        # c* A*
            if true or fb<=b then
                block:=bm[fb][b];
                for j in cand!.blockingmat[sb][b] do
                    ba:=fb/npgs.perm;
                    bb:=b/npgs.perm;
                    bc:=sb/npgs.perm;
                    bbl:=cand!.blocks[fb][b];
                    
                        
                    sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[icolor]][blkIdx[j]];
                od;
                if block<>[] then
                    npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
                fi;
                if fb<>sb and b<>sb and b<>fb and block<>[] then    # if block(=bm[fb][b]) is complete
                    if fbinfr and b in npgs.fullrows then
                        if not npgs.lbdIsForced  then  
                            npgs.lbdIsForced:=true;
                            npgs.lbd:=sq[block[1]];
                            if npgs.lbd<npgs.maxlbd then
                                stt[11]:=stt[11]+1;
                                return fail;
                            fi;
                        fi;
                        if ForAny(block, x->sq[x]<>npgs.lbd) then
                            stt[12]:=stt[12]+1;
                            return fail;
                        fi;
                    fi;
                fi;
                if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
                    stt[13]:=stt[13]+1;
                    return fail;
                fi;
            fi;
            
            if b<=fb then
                block:=bm[b][fb];   # A c
                for j in cand!.blockingmat[b][sb] do
                    ba:=b/npgs.perm;
                    bb:=fb/npgs.perm;
                    bc:=sb/npgs.perm;
                    bbl:=cand!.blocks[b][fb];
                    sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[j]][blkIdx[color]];
                od;
                if block<>[] then
                    npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
                fi;
                if fb<>sb and b<>sb and block<>[] then # if block(=bm[b][fb]) is complete
                    if  fbinfr and b in npgs.fullrows  then
                        if not npgs.lbdIsForced then
                            npgs.lbdIsForced:=true;
                            npgs.lbd:=sq[block[1]];
                            if npgs.lbd<npgs.maxlbd then
                                stt[14]:=stt[14]+1;
                                return fail;
                            fi;
                        fi;
                        if ForAny(block, x->sq[x]<> npgs.lbd) then
                            stt[15]:=stt[15]+1;
                            return fail;
                        fi;
                    fi;
                fi;
                if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
                    stt[16]:=stt[16]+1;
                    return fail;
                fi;
            fi;
        od;
    fi;
    block:=bm[sb][sb];      # c c*
    ba:=sb/npgs.perm;
    bb:=sb/npgs.perm;
    bc:=fb/npgs.perm;
    bbl:=cand!.blocks[sb][sb];
    sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[color]][blkIdx[icolor]];

    if block<>[] then
        npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
    fi;
    if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
        stt[17]:=stt[17]+1;
        return fail;
    fi;
        
    for b in cand!.ridx do      # c A*
        if true or sb<=b then
            block:=bm[sb][b];
            for j in cand!.blockingmat[fb][b] do
                ba:=sb/npgs.perm;
                bb:=b/npgs.perm;
                bc:=fb/npgs.perm;
                bbl:=cand!.blocks[sb][b];
                sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[color]][blkIdx[j]];
            od;
            if block<>[] then
                npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
            fi;
            if b<>sb  and block<>[] then   # if block(=bm[sb][b]) is complete
                if sbinfr and b in npgs.fullrows then
                    if not npgs.lbdIsForced then
                        npgs.lbdIsForced:=true;
                        npgs.lbd:=sq[block[1]];
                        if npgs.lbd<npgs.maxlbd then
                            stt[18]:=stt[18]+1;
                            return fail;
                        fi;
                    fi;
                    if ForAny(block, x->sq[x] <> npgs.lbd) then
                        stt[19]:=stt[19]+1;
                        return fail;
                    fi;
                fi;
            fi;
            if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
                stt[20]:=stt[20]+1;
                return fail;
            fi;
        fi;
        if b<=sb then
            block:=bm[b][sb]; # A c*
            for j in cand!.blockingmat[b][fb] do
                ba:=b/npgs.perm;
                bb:=sb/npgs.perm;
                bc:=fb/npgs.perm;
                bbl:=cand!.blocks[b][sb];
                sq{bbl}:=sq{bbl}+ent[ba][bb][bc][blkIdx[j]][blkIdx[icolor]];
            od;
            if block<>[] then
                npgs.maxlbd:=Maximum(npgs.maxlbd, Maximum(sq{block}));
            fi;
            if  block<>[] then # block (=bm[b][sb] is complete  
                if sbinfr and b in npgs.fullrows then 
                    if not npgs.lbdIsForced then 
                        npgs.lbdIsForced:=true;
                        npgs.lbd:=sq[block[1]];
                        if npgs.lbd<npgs.maxlbd then
                            stt[21]:=stt[21]+1;
                            return fail;
                        fi;
                    fi;
                    if ForAny(block, x->sq[x] <> npgs.lbd) then
                        stt[22]:=stt[22]+1;
                        return fail;
                    fi;
                fi;
            fi;
            if npgs.lbdIsForced and npgs.maxlbd> npgs.lbd then
                stt[23]:=stt[23]+1;
                return fail;
            fi;
        fi;
    od;
    
    if npgs.lbdIsForced then
        if sbinfr and ForAny(npgs.blockingmat[sb][sb], x->sq[x]<>npgs.lbd) then
            return fail;
        fi;
        if sb<>fb and fbinfr and ForAny(npgs.blockingmat[fb][fb], x->sq[x]<>npgs.lbd) then
            return fail;
        fi;
        if sb<>fb and sbinfr and fbinfr and ForAny(npgs.blockingmat[sb][fb], x->sq[x]<>npgs.lbd) then
            return fail;
        fi;
    fi;
    
            
    

    # if npgs.lbdIsForced then
    #     for i in [1..Length(npgs.fullrows)] do
    #         a:=npgs.fullrows[i];
    #         for j in [i..Length(npgs.fullrows)] do
    #             b:=npgs.fullrows[j];
    #             block:=npgs.blockingmat[a][b];
    #             if block <>[] then
    #                 if Length(Set(npgs.square{block}))>1 then
    #                     Error("Error 1");
    #                 fi;
    #                 if npgs.square[block[1]]<>npgs.lbd then
    #                     Error("Error 2");
    #                 fi;
    #             fi;
    #         od;
    #     od;
    # fi;
    
                
    Assert(1,sq=ComplexProduct(t,npgs.set,OnSets(npgs.set,Mates(t))));
    
    
            
    Objectify(NewType(GoodSetsFamily(t), IsSymPartialGoodSet and IsSymPartialGoodSetBlkRep), npgs);
    return npgs;
    
end);

InstallMethod(EmptySymPartialGoodSet,
        "for blocked tensors of structure constants",
        [IsTensor and IsTensorOfCC and IsBlockedTensorRep],
function(tensor)
    local mat,vec,perm,blocks,startBlock,finishBlock,rclr,clr,nof,imap,a,sclr,aclr,b,map,i,j,domdegreelist,cand,sb,bclr,idxBlk;
    
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
    domdegreelist:=ListWithIdenticalEntries(nof,0);
    for i in clr do
       sb:=startBlock[i];
       domdegreelist[sb]:=domdegreelist[sb]+OutValencies(tensor)[i];
    od;
    
    cand:=rec(tensor:=tensor,
              blocks:=blocks,
              perm:=perm,
              startBlock:=startBlock,
              finishBlock:=finishBlock,
              map:=map,
              imap:=imap,
              domain:=[1..Length(imap)],
              currentRow:=0,
              set:=[],
              maxlength:=Int((OrderOfTensor(tensor)-nof)/2),
              blockingmat:=List([1..nof], a->List([1..nof], b->[])),
              degreelist:=ListWithIdenticalEntries(nof,0),
              maxdeg:=0,
              maxlbd:=0,
              domdegreelist:=domdegreelist,
              ridx:=[],
              square:=ListWithIdenticalEntries(Order(tensor),0),
              fullrows:=[],
              kIsForced:=false,
              k:=0,
              lbdIsForced:=false,
              lbd:=0);
    
    return Objectify(NewType(GoodSetsFamily(tensor), IsSymPartialGoodSet and IsSymPartialGoodSetBlkRep), cand);
end);

##############################################################################
#
# Orbits of partial good sets
#
##############################################################################
DeclareRepresentation( "IsPartialGoodSetOrbitRep",
        IsCocoOrbitRep,
        [ "group",
          "rep",
          "stab",
          "act" ]);

InstallGlobalFunction(PartialGoodSetOrbitNC,
function(act,pgs,stab)
    local res;

    res:=rec(
             group:=Image(act),
             rep:=pgs,
             stab:=stab,
             act:=act );
   return Objectify(NewType(GoodSetOrbitFamily(TensorOfPartialGoodSet(pgs),PreImage(act)), IsPartialGoodSetOrbit and IsPartialGoodSetOrbitRep), res);
end);



##############################################################################
#
# the iterator for orbits of partial good sets 
#
##############################################################################

DeclareRepresentation( "IsPartialGoodSetOrbitIterRep", IsComponentObjectRep, ["state"]);

PartialGoodSetOrbitIteratorsFamily := NewFamily("PartialGoodSetOrbitIteratorsFamily", 
                                      IsIteratorOfPartialGoodSetOrbits);

InstallMethod(IteratorOfPartialGoodSetOrbits,
    "for symmetric partial good sets in PartialGoodSetRep",
    [IsPermGroup, IsPartialGoodSet],
function(aaut,cand)
    local S,SM,state,act;
    
    if not IsEmptyPartialGoodSet(cand) then
        ErrorNoReturn("IteratorOfPartialGoodSetOrbits: Expected an empty candidate as input.");
    fi;
    
    act:=ActionHomomorphism(aaut,IMapOfPartialGoodSet(cand),OnSets);
    
    S:=Stbc(Image(act));
    SM:=StbcCopy(S);
    
    state:=rec( cand:=cand,
                act:=act,
                S:=S,        
                SM:=SM,            
                M:=[],
                orbreps:=StbcMinimalOrbitReps(SM,DomainOfPartialGoodSet(cand)),
                orbidx:=1,
                linkback:=fail
               );
    
    return Objectify(NewType(PartialGoodSetOrbitIteratorsFamily,
                   IsIteratorOfPartialGoodSetOrbits and IsPartialGoodSetOrbitIterRep and IsMutable),
                   rec(state:=state));
end);


InstallMethod( NextIterator,
        "for iterators of partial good set orbits",
        [IsIteratorOfPartialGoodSetOrbits and IsPartialGoodSetOrbitIterRep and IsMutable],
function(iter)
    local NextState, res,cand;
        
    NextState:=function(state)
        local pt, SC, ncand, nextstate;
        
        if state=fail then 
            return fail; 
        fi;
        
        
        if not IsExtendiblePartialGoodSet(state.cand) then
            return NextState(state.linkback);
        fi;
        
        if state.orbidx>Length(state.orbreps) then
            return NextState(state.linkback);
        fi;
        
        ncand:=fail;
        # while ncand=fail and state.orbidx <= Length(state.orbreps) do 
        repeat
            pt:=state.orbreps[state.orbidx];
            state.orbidx:=state.orbidx+1;
            if IsCompatiblePoint(state.cand,pt) then

                ncand:=ExtendedPartialGoodSet(state.cand,pt);
                if ncand=nonext then
                    ncand:=fail;
                    break;
                fi;
                
                
                if ncand<>fail then
                    SC:=CocoSetReducibilityTest(state.S,state.SM,state.M,pt);
                    if IsPerm(SC) then
                        ncand:=fail;
                    fi;
                fi;
            fi;
        until ncand<>fail or state.orbidx > Length(state.orbreps);
        
        
        if ncand=fail then
            return NextState(state.linkback);
        fi;
        
            
        nextstate:=rec(cand:=ncand,
                       act:=state.act,
                       S:=state.S,
                       SM:=SC,
                       M:=Union(state.M,[pt]),
                       orbreps:=StbcMinimalOrbitReps(SC,DomainOfPartialGoodSet(ncand)),
                       orbidx:=1,
                       linkback:=state);
        return nextstate;
    end;
    
    if iter!.state=fail then
        return fail;
    fi;
    
    res:=PartialGoodSetOrbitNC(iter!.state.act, iter!.state.cand, StbcGroup(iter!.state.SM));
    iter!.state:=NextState(iter!.state);
    return res;
end);


InstallMethod( IsDoneIterator,
        "for iterators of good set cands",
        [IsIteratorOfPartialGoodSetOrbits and IsPartialGoodSetOrbitIterRep],
function(iter)
    return iter!.state=fail;
end);

InstallMethod( ViewString,
        "for set orbit iterators",
        [IsIteratorOfPartialGoodSetOrbits and IsPartialGoodSetOrbitIterRep],
function(iter)
    if iter!.state=fail then
        return "<done good set orbit iterator>";
    else
        return Concatenation("<good set orbit iterator, current set ",
                             String(iter!.state.M), ">");
    fi;
end);         
         
COCOInfoGSSize:=10;
InstallMethod(AllGoodSetOrbits,
        "for iterators of good set candidates",
        [IsIteratorOfPartialGoodSetOrbits and IsPartialGoodSetOrbitIterRep],
function(iter)
    local res,gens,stab,grp,gs;
    
    if IsDoneIterator(iter) then
        return [];
    fi;
    
    res:=[];
    grp:=Source(iter!.state.act);
    
    while not IsDoneIterator(iter) do
        if Length(iter!.state.M)<=COCOInfoGSSize then
            Info(InfoCOCO,1,iter!.state.M,"\n");
        fi;
        
        
        if IsCompletePartialGoodSet(iter!.state.cand) then
            gs:=GoodSetFromPartialGoodSet(iter!.state.cand);
            if gs <> fail then 
                gens:=ShallowCopy(iter!.state.SM.generators);
                stab:=Group(PreImagesSet(iter!.state.act,gens),());            
                Add(res, GoodSetOrbit(grp,gs, stab));
                Info(InfoCOCO,1,"*");
            fi;
        fi;
        
        NextIterator(iter);
    od;
    return res;
end);

# InstallMethod(ConstructorOfCocoOrbit,
#         "for all partial good set orbits",
#         [IsPartialGoodSetOrbit],
# function(orb)
#     return PartialGoodSetOrbit;
# end);

InstallMethod(ConstructorOfCocoOrbitNC,
        "for all partial good set orbits",
        [IsPartialGoodSetOrbit],
function(orb)
    return PartialGoodSetOrbitNC;
end);
