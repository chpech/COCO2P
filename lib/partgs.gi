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
        "for partialgood sets in PartialGoodSetRep",
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
    local part,sqr,set;
       
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
          "kIsKnown",
          "k",
          "lbdIsKnown",
          "lbd"
          ]);


InstallMethod(IsCompletePartialGoodSet,
    "for asymmetric partial good sets in AsymPartialGoodSetBlkRep",
    [IsAsymPartialGoodSet and IsAsymPartialGoodSetBlkRep],
function(cand)
    local cdegs;
    
    if not cand!.kIsKnown or not cand!.lbdIsKnown then
        return false;
    fi;
    
    if not Length(cand!.fullrows)=Length(cand!.blocks) then
        return false;
    fi;
    
    cdegs:=cand!.coldegs;
    if ForAny([2..Length(cdegs)], i->cdegs[1]<>cdegs[i]) then
        return false;
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
function(cand,i)
    local t,color, sb,fb,rx,cx,fr,bm,sd,rd,cd,sq,nd,ndrd,ndcd,j,k,kmts,obj,cm,blk,rm,icolor,nxtdomrow,newnxtdom,ksb,kfb,kIsKnown,kk,md,kcolors,sbinfr,lbd,lbdIsKnown;

    t:=cand!.tensor;
    color:=cand!.imap[i][1];
    sb:=cand!.startBlock[color];
    fb:=cand!.finishBlock[color];
    
    kIsKnown:=cand!.kIsKnown;
    kk:=cand!.k;

   
    rx:=ShallowCopy(cand!.ridx);
    AddSet(rx, sb);
    cx:=ShallowCopy(cand!.cidx);
    AddSet(cx, fb);

    
    
    bm:=ShallowCopy(cand!.blockingmat);
    bm[sb]:=ShallowCopy(bm[sb]);
    bm[sb][fb]:=ShallowCopy(bm[sb][fb]);
    AddSet(bm[sb][fb],color);   
   
    sd:=OutValencies(t);
    rd:=ShallowCopy(cand!.rowdegs);
    cd:=ShallowCopy(cand!.coldegs);

    rd[sb]:=rd[sb]+sd[color];
    rm:=Maximum(rd[sb], cand!.rmaxdeg);
    icolor:=color^Mates(t);
    cd[fb]:=cd[fb]+sd[icolor];
    cm:=Maximum(cd[fb], cand!.cmaxdeg);    
    md:=Maximum(rm,cm);
    
    if not kIsKnown then
        if sb>1 then
            fr:=[1..sb-1];
            kIsKnown:=true;
            kk:=rd[1];
            if ForAny([2..sb-1], x->rd[x]<>kk) then
                return fail;
            fi;
        else
            fr:=[];
        fi;
    else
        fr:=ShallowCopy(cand!.fullrows);
        if rd[sb]=kk then
            AddSet(fr,sb);
        fi;
    fi;
    if kIsKnown and md > kk then
        return fail;
    fi;
    
    sbinfr:=(sb in fr);
    
    lbdIsKnown:=cand!.lbdIsKnown;
    lbd:=cand!.lbd;
    
    sq:=ShallowCopy(cand!.square); 
    for blk in cand!.ridx do
        for j in cand!.blockingmat[blk][fb] do
            for k in cand!.blocks[blk][sb] do
                sq[k]:=sq[k]+EntryOfTensor(t,j,icolor,k);
            od;
            if lbdIsKnown and ForAny(bm[blk][sb], k->sq[k]>lbd) then
                return fail;
            fi;
        od;
        if not lbdIsKnown and sbinfr and (blk in fr) 
           and sb<>blk 
           and bm[blk][sb]<>[] then
            lbdIsKnown:=true;
            lbd:=sq[bm[blk][sb][1]];
            if ForAny([2..Length(bm[blk][sb])], 
                      x->sq[bm[blk][sb][x]]<> lbd) then
                return fail;
            fi;
        fi;
    od;
    for blk in cand!.ridx do
        for j in cand!.blockingmat[blk][fb] do
            for k in cand!.blocks[sb][blk] do
                sq[k]:=sq[k]+EntryOfTensor(t,color,j^Mates(t),k);
            od;
            if lbdIsKnown and ForAny(bm[sb][blk], k->sq[k]>lbd) then
                return fail;
            fi;
        od;
        if not lbdIsKnown and sbinfr and (blk in fr) 
           and sb<>blk 
           and bm[sb][blk]<>[] then
            lbdIsKnown:=true;
            lbd:=sq[bm[sb][blk][1]];
            if ForAny([2..Length(bm[sb][blk])], 
                      x->sq[bm[sb][blk][x]]<> lbd) then
                return fail;
            fi;
        fi;
    od;
    
    for k in cand!.blocks[sb][sb] do
        sq[k]:=sq[k]+EntryOfTensor(t,color,icolor,k);
    od;
    
    if not lbdIsKnown and sbinfr and bm[sb][sb]<>[] then
        lbdIsKnown:=true;
        lbd:=sq[bm[sb][sb][1]];
        if ForAny([2..Length(bm[sb][sb])], 
                  x->sq[bm[sb][sb][x]]<> lbd) then
            return fail;
        fi;
    fi;

    if cand!.lbdIsKnown and ForAny(bm[sb][sb], k->sq[k]>cand!.lbd) then
        return fail;
    fi;
 
    nd:=[];
    ndrd:=ShallowCopy(cand!.domrowdegs);
    ndcd:=ShallowCopy(cand!.domcoldegs);
    for k in cand!.domain do
#        k:=cand!.domain[j];
        kmts:=[cand!.imap[k][1],cand!.imap[k][1]^Mates(t)];
        ksb:=cand!.startBlock[kmts[1]];
        kfb:=cand!.finishBlock[kmts[1]];
        if k<=i  
           or kmts[1]=color^Mates(t) 
           or ksb in fr  
           or kIsKnown and (sd[kmts[1]]+rd[ksb]>kk or sd[kmts[2]]+cd[kfb]>kk) 
           then
            ndrd[ksb]:=ndrd[ksb]-sd[kmts[1]];
            ndcd[kfb]:=ndcd[kfb]-sd[kmts[2]];
            if ndrd[ksb]+rd[ksb]<md or ndcd[kfb]+cd[kfb]<md then
                return fail;
            fi;
            continue;
        else 
            Add(nd,k);
        fi;
        
    od;
    
    obj:=rec(tensor:=cand!.tensor,
             blocks:=cand!.blocks,
             startBlock:=cand!.startBlock,
             finishBlock:=cand!.finishBlock,
             map:=cand!.map,
             imap:=cand!.imap,
             domain:=nd,
             currentRow:=sb,
             set:=Union(cand!.set, [color]),
             maxlength:=cand!.maxlength,
             blockingmat:=bm,
             rowdegs:=rd,
             coldegs:=cd,
             rmaxdeg:=rm,
             cmaxdeg:=cm,
             domrowdegs:=ndrd,
             domcoldegs:=ndcd,
             ridx:=rx,
             cidx:=cx,
             square:=sq,
             fullrows:=fr,
             kIsKnown:=kIsKnown,
             k:=kk,
             lbdIsKnown:=lbdIsKnown,
             lbd:=lbd);
    
    # Assert(1,obj.rowdegs=RowDegreeList(obj.tensor,obj.set),"!!!!!!!!!!!!!!A");
    # Assert(1,obj.coldegs=ColDegreeList(obj.tensor,obj.set),"!!!!!!!!!!!!!!B");
    # Assert(1,obj.blockingmat=BlockingMat(obj.tensor,obj.set),"!!!!!!!!!!!!!!C");
    # Assert(1,obj.domrowdegs=RowDegreeList(obj.tensor,Union(List(obj.domain,x->obj.imap[x]))),"!!!!!!!!!!!!!!D");
    # Assert(1,obj.domrowdegs=RowDegreeList(obj.tensor,Union(List(obj.domain,x->obj.imap[x]))));
    # Assert(1,obj.domcoldegs=ColDegreeList(obj.tensor,Union(List(obj.domain,x->obj.imap[x]))),"!!!!!!!!!!!!!!E");
    # Assert(1,obj.ridx=Set(obj.set,x->StartBlock(obj.tensor,x)),"!!!!!!!!!!!!!!F");
    # Assert(1,obj.cidx=Set(obj.set,x->FinishBlock(obj.tensor,x)),"!!!!!!!!!!!!!!G");
    # Assert(1,obj.square=ComplexProduct(obj.tensor,obj.set,obj.set),"!!!!!!!!!!!!!!H");
    # Assert(obj.rmaxdeg=Maximum(obj.rowdegs),"!!!!!!!!!!!!!!I");
    # Assert(1,obj.cmaxdeg=Maximum(obj.coldegs),"!!!!!!!!!!!!!!J");
    # Assert(1,function() 
    #     if Length(obj.rowdegs)>1 then
    #         if obj.rowdegs[2]<>0 then
    #             if obj.fullrows <> Filtered([1..Length(obj.rowdegs)], i->obj.rowdegs[i] = obj.rowdegs[1]) then
    #                 return false;
    #             fi;
    #         fi;
    #     fi;return true;
    # end(),"!!!!!!!!!!!!!!K");
    
    return Objectify(NewType(GoodSetsFamily(t), IsAsymPartialGoodSet and IsAsymPartialGoodSetBlkRep), obj);
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
#    grp:=ClosureGroup(aaut,Mates(tensor));
#    act:=ActionHomomorphism(grp,imap,OnPoints);
  
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
              domrowdegs:=domrowdegs,
              domcoldegs:=domcoldegs,
              ridx:=[],
              cidx:=[],
              square:=ListWithIdenticalEntries(Order(tensor),0),
              fullrows:=[],
              kIsKnown:=false,
              k:=0,
              lbdIsKnown:=false,
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
          "domdegreelist",
          "ridx",
          "square",
          "fullrows",
          "kIsKnown",
          "k",
          "lbdIsKnown",
          "lbd"
          ]);

InstallMethod(IsCompletePartialGoodSet,
    "for symmetric partial good sets in SymPartialGoodSetBlkRep",
    [IsSymPartialGoodSet and IsSymPartialGoodSetBlkRep],
function(cand)
    if not cand!.kIsKnown or not cand!.lbdIsKnown then
        return false;
    fi;
    
    if not Length(cand!.fullrows)=Length(cand!.blocks) then
        return false;
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
    
    if IsSubset(cand!.fullrows, [cand!.currentRow..pos-1]) then
#        Assert(1,IsSubset(Union(cand!.fullrows,[cand!.currentRow]), [1..pos-1]));
        
        return true;
    fi;
    return false;
end);

testflag:=false;

testlbd:=function(cand)
    local a,b,subdeg;
    
    for a in cand!.fullrows do
        for b in cand!.fullrows do
            if cand!.blockingmat[a][b]<>[] then
                subdeg:=Set(cand!.square{cand!.blockingmat[a][b]});
                return subdeg[1];
            fi;
        od;
    od;
    return fail;
end;

InstallMethod(ExtendedPartialGoodSet,
    "for symmetric partial good sets in SymPartialGoodSetBlk",
    [IsSymPartialGoodSet and IsSymPartialGoodSetBlkRep, IsPosInt],
function(cand,i)
    local t,color,icolor,sb,fb,set,rx,fr,bm,sd,dl,md,sq,blk,j,k,nd,nddl,kmts,obj,ksb,kfb,kIsKnown,kk,fbinfr,sbinfr,lbdIsKnown,lbd,kAll,kA,ncand,a,b;
    
    t:=cand!.tensor;
    
    color:=cand!.imap[i][1];
    icolor:=color^Mates(t);
    sb:=cand!.startBlock[color];
    fb:=cand!.finishBlock[color];
    
    if fb<sb then
        color:=cand!.imap[i][2];
        icolor:=cand!.imap[i][1];
        sb:=cand!.startBlock[color];
        fb:=cand!.finishBlock[color];
    fi;
    set:=Union(cand!.set, [color,icolor]);
    
    kIsKnown:=cand!.kIsKnown;
    kk:=cand!.k;
    lbdIsKnown:=cand!.lbdIsKnown;
    lbd:=cand!.lbd;
    
    
    fr:=ShallowCopy(cand!.fullrows);
    if not kIsKnown then
        if sb>1 then
            kIsKnown:=true;
            kk:=cand!.degreelist[1];
            if ForAny([2..sb-1], x->cand!.degreelist[x]<>kk) then
                return fail;
            fi;
            fr:=Filtered([1..Length(cand!.blocks)], x->cand!.degreelist[x]=kk);
            for a in fr do
                for b in fr do
                    kA:=cand!.blockingmat[a][b];
                    if not lbdIsKnown and kA<>[] then
                        lbdIsKnown:=true;
                        lbd:=cand!.square[kA[1]];
                    fi;
                    if lbdIsKnown and ForAny([2..Length(kA)], k->cand!.square[kA[k]]<>lbd) then
                        return fail;
                    fi;
                od;
            od;
        fi;
    fi;
    
    rx:=ShallowCopy(cand!.ridx);
    AddSet(rx,sb);
    AddSet(rx,fb);
    
    bm:=ShallowCopy(cand!.blockingmat);
    bm[sb]:=ShallowCopy(bm[sb]);
    bm[sb][fb]:=ShallowCopy(bm[sb][fb]);
    AddSet(bm[sb][fb],color);
    
    sd:=OutValencies(t);
    dl:=ShallowCopy(cand!.degreelist);
    
    dl[sb]:=dl[sb]+sd[color];
    md:=Maximum(cand!.maxdeg, dl[sb]);
    if color<>icolor then
        if fb<>sb then
            bm[fb]:=ShallowCopy(bm[fb]);
            bm[fb][sb]:=ShallowCopy(bm[fb][sb]);
        fi;
        AddSet(bm[fb][sb],icolor);
        dl[fb]:=dl[fb]+sd[icolor];
        md:=Maximum(md, dl[fb]);
    fi;
    if dl[sb]=kk then
        AddSet(fr,sb);
    fi;
    if sb<>fb and dl[fb]=kk then
        AddSet(fr, fb);
    fi;

    if kIsKnown and md > kk then
        return fail;
    fi;
    
    fbinfr:=(fb in fr);
    sbinfr:=(sb in fr);
    
    sq:=ShallowCopy(cand!.square);
    
    if color<>icolor then
        for blk in cand!.ridx do        # Ac
            kAll:=cand!.blocks[blk][fb];kA:=bm[blk][fb];
            for j in cand!.blockingmat[blk][sb] do
                for k in kAll do
                    sq[k]:=sq[k]+EntryOfTensor(t,j,color,k);
                od;
                if lbdIsKnown and ForAny(kA, k->sq[k]>lbd) then
                    return fail;
                fi;
            od;
            if not lbdIsKnown and fbinfr and blk in fr  
               and sb<>fb and fb<>blk 
               and kA<>[] then
                lbdIsKnown:=true;
                lbd:=sq[kA[1]];
                if ForAny([2..Length(kA)], 
                          k->sq[kA[k]]<> lbd) then
                    return fail;
                fi;
            fi;
        od;
        for blk in cand!.ridx do        # c*A*
            kAll:=cand!.blocks[fb][blk];kA:=bm[fb][blk];
            for j in cand!.blockingmat[sb][blk] do
                for k in kAll do
                    sq[k]:=sq[k]+EntryOfTensor(t,icolor,j,k);
                od;
                if lbdIsKnown and ForAny(kA, k->sq[k]>lbd) then
                    return fail;
                fi;
            od;
            if not lbdIsKnown and fbinfr and blk in fr  
               and sb<>fb and fb<>blk 
               and kA<>[] then
                lbdIsKnown:=true;
                lbd:=sq[kA[1]];
                if ForAny([2..Length(kA)], 
                          k->sq[kA[k]]<> lbd) then
                    return fail;
                fi;
            fi;
        od;
        kAll:=cand!.blocks[fb][fb];kA:=bm[fb][fb];      # c*c
        for k in kAll do
            sq[k]:=sq[k]+EntryOfTensor(t,icolor,color,k);
        od;
        if not lbdIsKnown and fbinfr
           and sb<>fb
           and kA<>[] then
            lbdIsKnown:=true;
            lbd:=sq[kA[1]];
            if ForAny([2..Length(kA)], 
                      k->sq[kA[k]]<>lbd) then
                return fail;
            fi;
        fi;
        if cand!.lbdIsKnown and ForAny(kA, k->sq[k]>cand!.lbd) then
            return fail;
        fi;
        
        if sb=fb then
            kAll:=cand!.blocks[sb][fb];kA:=bm[sb][fb];      # cc,c*c*
            for k in kAll do
                sq[k]:=sq[k]+EntryOfTensor(t,color,color,k);
                sq[k]:=sq[k]+EntryOfTensor(t,icolor,icolor,k);
            od;
            if not lbdIsKnown and sbinfr
               and kA<>[] then
                lbdIsKnown:=true;
                lbd:=sq[kA[1]];
                if ForAny([2..Length(kA)], 
                          k->sq[kA[k]]<>lbd) then
                    return fail;
                fi;
            fi;
            if cand!.lbdIsKnown and ForAny(kA, k->sq[k]>cand!.lbd) then
                return fail;
            fi;
        fi;
    fi;

    for blk in cand!.ridx do        # Ac*
        kAll:=cand!.blocks[blk][sb];kA:=bm[blk][sb];
        for j in cand!.blockingmat[blk][fb] do
            for k in kAll do
                sq[k]:=sq[k]+EntryOfTensor(t,j,icolor,k);
            od;
            if lbdIsKnown and ForAny(kA, k->sq[k]>lbd) then
                return fail;
            fi;
        od;
        if not lbdIsKnown and sbinfr and blk in fr  
           and  sb<>blk 
           and kA<>[] then
            lbdIsKnown:=true;
            lbd:=sq[kA[1]];
            if ForAny([2..Length(kA)], 
                      k->sq[kA[k]] <> lbd) then
                return fail;
            fi;
        fi;
    od;
    for blk in cand!.ridx do      # cA*
        kAll:=cand!.blocks[sb][blk];kA:=bm[sb][blk];
        for j in cand!.blockingmat[fb][blk] do
            for k in kAll do
                sq[k]:=sq[k]+EntryOfTensor(t,color,j,k);
            od;
            if lbdIsKnown and ForAny(kA, k->sq[k]>lbd) then
                return fail;
            fi;
        od;
        if not lbdIsKnown and sbinfr and blk in fr 
           and  sb<>blk 
           and kA<>[] then
            lbdIsKnown:=true;
            lbd:=sq[kA[1]];
            if ForAny([2..Length(kA)], 
                      k->sq[kA[k]] <> lbd) then
                return fail;
            fi;
        fi;
    od;
    
    
    
    
    kAll:=cand!.blocks[sb][sb];kA:=bm[sb][sb];      # cc*
    for k in kAll do
        sq[k]:=sq[k]+EntryOfTensor(t,color,icolor,k);
    od;
    if not lbdIsKnown and sbinfr
    #   and sb<>fb
       and kA<>[] then
        lbdIsKnown:=true;
        lbd:=sq[kA[1]];
        if ForAny([2..Length(kA)], 
                  k->sq[kA[k]] <> lbd) then
            return fail;
        fi;
    fi;
    if cand!.lbdIsKnown and ForAny(kA, k->sq[k]>cand!.lbd) then
        return fail;
    fi;
    
    
   Assert(1,sq=ComplexProduct(t,set,OnSets(set,Mates(t))));
    
    
    nd:=[];
    nddl:=ShallowCopy(cand!.domdegreelist);
    for j in [1..Length(cand!.domain)] do
        k:=cand!.domain[j];
        kmts:=cand!.imap[k];
        ksb:=cand!.startBlock[kmts[1]];
        kfb:=cand!.finishBlock[kmts[1]];
        if k<=i 
           or ksb in fr
           or kfb in fr
           or kIsKnown and (sd[kmts[1]]+dl[ksb]>kk 
                   or  (Length(kmts)=2 and sd[kmts[2]]+dl[kfb]>kk))
           then
            nddl[ksb]:=nddl[ksb]-sd[kmts[1]];
            if nddl[ksb]+dl[ksb]<md then
                return fail;
            fi;
            if Length(kmts)=2 then
                nddl[kfb]:=nddl[kfb]-sd[kmts[2]];
                if nddl[kfb]+dl[kfb]<md then
                    return fail;
                fi;
            fi;
        else
            Add(nd,k);
        fi;
    od;
    
    obj:=rec(tensor:=cand!.tensor,
             blocks:=cand!.blocks,
             startBlock:=cand!.startBlock,
             finishBlock:=cand!.finishBlock,
             map:=cand!.map,
             imap:=cand!.imap,
             domain:=nd,
             currentRow:=sb,
             set:=set,
             maxlength:=cand!.maxlength,
             blockingmat:=bm,
             degreelist:=dl,
             maxdeg:=md,
             domdegreelist:=nddl,
             ridx:=rx,
             square:=sq,
             fullrows:=fr,
             kIsKnown:=kIsKnown,
             k:=kk,
             lbdIsKnown:=lbdIsKnown,
             lbd:=lbd);
    # Assert(1,obj.degreelist=RowDegreeList(obj.tensor,obj.set),"??????????????A");
    # Assert(1,obj.blockingmat=BlockingMat(obj.tensor, obj.set),"??????????????B");
    # Assert(1,obj.domdegreelist=RowDegreeList(obj.tensor,Union(List(obj.domain,x->obj.imap[x]))),"??????????????C");
    # Assert(1,obj.domdegreelist=RowDegreeList(obj.tensor,Union(List(obj.domain,x->obj.imap[x]))));
    # Assert(1,obj.ridx=Set(obj.set,x->StartBlock(obj.tensor,x)),"??????????????D");
    # Assert(1,obj.square=ComplexProduct(obj.tensor,obj.set,obj.set),"??????????????E");
    # Assert(1,obj.maxdeg=Maximum(obj.degreelist),"??????????????F");
    # Assert(1,function() if Length(obj.degreelist)>1 then
    #         if  ForAny(obj.set, x->StartBlock(obj.tensor,x)>1 and FinishBlock(obj.tensor,x)>=StartBlock(obj.tensor,x)) then
    #             if obj.fullrows <> Filtered([1..Length(obj.degreelist)], i->obj.degreelist[i] = obj.degreelist[1])  then
    #                 return false;
    #             fi;
    #         fi;
    #     fi; return true;
    # end(), "??????????????G");
    
   
    ncand:=Objectify(NewType(GoodSetsFamily(t), IsSymPartialGoodSet and IsSymPartialGoodSetBlkRep), obj);
    # if testlbd(ncand) <> fail and not ncand!.lbdIsKnown then
    #     Error("lbd should be known!");
    # fi;
    
    return ncand;
    
end);






InstallMethod(EmptySymPartialGoodSet,
        "for blocked tensors of structure constants",
        [IsTensor and IsTensorOfCC and IsBlockedTensorRep],
function(tensor)
    local mat,vec,perm,blocks,startBlock,finishBlock,rclr,clr,nof,imap,a,sclr,aclr,b,map,i,j,domdegreelist,cand,sb,bclr;
    
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
              domdegreelist:=domdegreelist,
              ridx:=[],
              square:=ListWithIdenticalEntries(Order(tensor),0),
              fullrows:=[],
              kIsKnown:=false,
              k:=0,
              lbdIsKnown:=false,
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
        while ncand=fail and state.orbidx <= Length(state.orbreps) do 
            repeat
                pt:=state.orbreps[state.orbidx];
                state.orbidx:=state.orbidx+1;
                if IsCompatiblePoint(state.cand,pt) then
                    SC:=CocoSetReducibilityTest(state.S,state.SM,state.M,pt);
                else
                    SC:=();
                fi;
            until not IsPerm(SC) or state.orbidx > Length(state.orbreps);
            if IsPerm(SC) then
                return NextState(state.linkback);
            fi;
            ncand:=ExtendedPartialGoodSet(state.cand,pt);
            # if state.M=[ 1, 3, 16, 18, 27, 30,33] and pt=34 then # IsSubset([ 1, 3, 16, 18, 27, 30, 33, 34 ], Union(state.M,[pt])) and ncand=fail then
            #     testflag:=true;
            #     ncand:=ExtendedPartialGoodSet(state.cand,pt);
            #     Error("?????");
            # fi;
            
        od;
        
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
    return Concatenation("<good set orbit iterator, current set ",
          String(iter!.state.M), ">");
end);         
         
COCOInfoGSSize:=15;
InstallMethod(AllGoodSetOrbits,
        "for iterators of good set candidates",
        [IsIteratorOfPartialGoodSetOrbits and IsPartialGoodSetOrbitIterRep],
function(iter)
    local res,T,gens,stab,grp,gs;
    
    if IsDoneIterator(iter) then
        return [];
    fi;
    
    res:=[];
    T:=TensorOfPartialGoodSet(iter!.state.cand);
    grp:=Source(iter!.state.act);
    
    while not IsDoneIterator(iter) do
        if Length(iter!.state.M)<=COCOInfoGSSize then
            COCOPrint(iter!.state.M);
            if iter!.state.cand!.kIsKnown then
                COCOPrint("(",iter!.state.cand!.k);
            fi;
            if iter!.state.cand!.lbdIsKnown then
                COCOPrint(",",iter!.state.cand!.lbd);
            fi;
            COCOPrint(")\n");
        fi;
        
        if IsCompletePartialGoodSet(iter!.state.cand) then
            gs:=GoodSetFromPartialGoodSet(iter!.state.cand);
            if gs <> fail then 
                gens:=ShallowCopy(iter!.state.SM.generators);
                stab:=Group(PreImagesSet(iter!.state.act,gens),());            
                Add(res, GoodSetOrbit(grp,gs, stab));
            fi;
        fi;
        
        NextIterator(iter);
    od;
    return res;
end);
