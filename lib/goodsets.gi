############################################
##  $Id: goodsets.gi,v 1.1 2009-01-05 22:43:41+01 zeka Exp zeka $
##
##  $Log: goodsets.gi,v $
##  Revision 1.1  2009-01-05 22:43:41+01  zeka
##  a first complete version of the good-sets algorithm
##
##  Revision 1.0  2008-12-23 18:32:18+01  zeka
##  Initial revision
##
##
############################################

Revision.goosets_gi :=
  "@(#)$Id: goodsets.gi,v 1.1 2009-01-05 22:43:41+01 zeka Exp zeka $";


#############################################################################
##
##  goodsets.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of good sets
##
#############################################################################

RowDegreeList:=function(T,M)
    local i,res,sb;
    res:=List([1..NumberOfFibres(T)], x->0);
    for i in M do
       sb:=StartBlock(T,i);
       res[sb]:=res[sb]+OutValencies(T)[i];
    od;
    return res;
end;

ColDegreeList:=function(T,M)
    local i,res,fb;
    res:=List([1..NumberOfFibres(T)], x->0);
    for i in M do
       fb:=FinishBlock(T,i);
       res[fb]:=res[fb]+OutValencies(T)[i^Mates(T)];
    od;
    return res;
end;

DeclareRepresentation("IsGoodSetCandRep",
        IsAttributeStoringRep,
        [ "tensor",             # the tensor over which the candidate "lives"
          "set",                # a subset of colors of <tensor>
          "nperm",              # the normalizing permutation
          "nset",               # the normalized version of set (must be minimal in its set-orbit under naut)
          "maxlength",          # the maximal length a goodset
          "ndomain",            # asymmetric normalized colors that are still in stock
        ]);

DeclareRepresentation("IsAsymGoodSetCandRep",
        IsGoodSetCandRep,
        [ "tensor",             # the tensor over which the candidate "lives"
          "set",                # a subset of colors of <tensor>
          "nperm",              # the normalizing permutation
          "nset",               # the normalized version of set (must be minimal in its set-orbit under naut)
          "bcols",              # the block-columns to which colors from <set> have to belong
          "brows",              # the block rows to which colors from <set> have to belong
          "maxlength",          # the maximal length of a good set
          "blockingmat",        # the blocking-matrix of the colors from <set>
          "rowdegs",            # for each block the out-valency of the set in this block
          "coldegs",            #
          "rmaxdeg",            # the maximum of rowdegs
          "cmaxdeg",            # the maximum of coldegs
          "ndomain",            # asymmetric normalized colors that are still in stock
          "ndomrowdegs",        # the RowDegreeList of ndomain
          "ndomcoldegs",        # the ColDegreeList of ndomain
          "ridx",               # block rows from which colors have been chosen
          "cidx",               # block columns from which colors have been chosen
          "regflag",            # true if we are searching for a regular asym. good set
          "square",             # set * set^Mates(tensor) (in normalized order)
          "fullrows"            # block rows that are already full
        ]);

DeclareRepresentation("IsSymGoodSetCandRep",
        IsGoodSetCandRep,
        [ "tensor",             # the tensor over which the candidate "lives"
          "set",                # a subset of colors of <tensor>
          "nperm",              # the normalizing permutation
          "nset",               # the normalized version of set (must be minimal in its set-orbit under naut)
          "blks",               # the block- and row-columns to which colors from <set> have to belong
          "maxlength",          # the maximal length of a good set
          "blockingmat",        # the blocking-matrix of the colors from <set>
          "degreelist",         # for each block the out-valency of the set in this block
          "maxdeg",             # the maximum of rowdegs
          "ndomain",            # asymmetric normalized colors that are still in stock
          "ndomdegreelist",     # the DegreeList of ndomain
          "ridx",               # block rows from which colors have been chosen
          "square",             # set * set^Mates(tensor) (in normalized order)
          "fullrows"            # block rows that are already full
        ]);


# this function returns a permutation that reorders the colors (=vertices)
# of the tensor in a way that
# 1.) reflexive colors get numbers 1..nof (so every reflexive color is remaped to its rowblk(=colblk))
# 2.) the non-reflexive colors are ordered by rowblk and colblk. So after resorting they are enumerated like this:
#         - first come the colors from block [1,1], then from [1,2], etc, then [1,nof]
#         - then [2,1], [2,2], ..., [2,nof] etc
#         - at the end come the colors from block [nof,nof]
# A structure constants tensor whose colors are sorted in this way, is called "normalized"
InstallGlobalFunction(GetNormalizingPermutationForAsymCandidate,
function(tensor)
    local   rcol,  col,  nof,  map,  blkmat,  i,  a,  ir,  r,  blk,  
            b;
    
    
    rcol:=ReflexiveColors(tensor);
    col:=Difference([1..OrderOfTensor(tensor)], rcol);
    nof:=Length(rcol);
    map:=ShallowCopy(rcol);
    
    blkmat:=List([1..nof], x->List([1..nof], x->[]));
    for i in col do
        Add(blkmat[StartBlock(tensor, i)][FinishBlock(tensor,i)], i);
    od;
    
    
    
   for a in [1..nof] do
     for b in [1..nof] do
        Append(map, blkmat[a][b]);
     od;
   od;
   return PermList(map)^-1;
end);

InstallGlobalFunction(GetNormalizingPermutationForSymCandidate,
function(tensor)
    local   rcol,  col,  nof,  map,  blkmat,  i,  a,  sclr,  aclr,  b;
    
    
    rcol:=ReflexiveColors(tensor);
    col:=Difference([1..OrderOfTensor(tensor)], rcol);
    nof:=Length(rcol);
    map:=ShallowCopy(rcol);
    
    blkmat:=List([1..nof], x->List([1..nof], x->[]));
    for i in col do
        Add(blkmat[StartBlock(tensor, i)][FinishBlock(tensor,i)], i);
    od;
    
    for a in [1..nof] do
        sclr:=Filtered(blkmat[a][a], x->x^Mates(tensor)=x);
        aclr:=Filtered(blkmat[a][a], x->x<x^Mates(tensor));
        blkmat[a][a]:=Concatenation(sclr, Concatenation(List(aclr, x->[x,x^Mates(tensor)])));
    od;
    
    for a in [1..nof] do
        Append(map, blkmat[a][a]);
        for b in [a+1..nof] do
            Append(map, Concatenation(List(blkmat[a][b], x->[x,x^Mates(tensor)])));
        od;
    od;
    return PermList(map)^-1;
end);

InstallGlobalFunction(EmptyAsymGoodSetCandHom,
function(tensor)
   local h,res,clr;

   if not IsHomogeneous(tensor) then
      return fail;
   fi;
   h:=GetNormalizingPermutationForAsymCandidate(tensor);
   clr:=Difference([1..OrderOfTensor(tensor)], ReflexiveColors(tensor));
   clr:=Filtered(clr, x->x^Mates(tensor)<>x);
   res:=rec(tensor:=tensor,
            set:=[],
            nperm:=h,
            nset:=[],
            ndomain:=OnSets(clr, h),
            maxlength:=Minimum(Length(clr)/2, Int((OrderOfTensor(tensor)-Length(ReflexiveColors(tensor)))/2)));
   return Objectify(NewType(GoodSetsFamily(tensor), IsAsymGoodSetCandidate and IsGoodSetCandRep), res);
end);

InstallGlobalFunction(EmptySymGoodSetCandHom,
function(tensor)
   local h,res,clr;

   if not IsHomogeneous(tensor) then
      return fail;
   fi;
   h:=GetNormalizingPermutationForSymCandidate(tensor);
   clr:=Difference([1..OrderOfTensor(tensor)], ReflexiveColors(tensor));
   res:=rec(tensor:=tensor,
            set:=[],
            nperm:=h,
            nset:=[],
            ndomain:=OnSets(clr, h),
            maxlength:=Minimum(Length(clr), Int((OrderOfTensor(tensor)-Length(ReflexiveColors(tensor)))/2)));
   return Objectify(NewType(GoodSetsFamily(tensor), IsSymGoodSetCandidate and IsGoodSetCandRep), res);
end);


InstallGlobalFunction(EmptySymGoodSetCandidate,
function(tensor,blks)
   local res,nof,clr,h;

   nof:=NumberOfFibres(tensor);
   h:=GetNormalizingPermutationForSymCandidate(tensor);
   clr:=Difference([1..OrderOfTensor(tensor)], ReflexiveColors(tensor));
   clr:=Filtered(clr, x->StartBlock(tensor,x) in blks and FinishBlock(tensor,x) in blks);
   res:=rec(tensor:=tensor,
            set:=[],
            nperm:=h,
            nset:=[],
            blks:=blks,
            maxlength:=Minimum(Length(clr),Int((OrderOfTensor(tensor)-Length(ReflexiveColors(tensor)))/2)),
            blockingmat:=List([1..nof], a->List([1..nof], b->[])),
            degreelist:=List([1..nof], x->0),
            maxdeg:=0,
            ndomain:=Set(clr, x->x^h),
            ndomdegreelist:=RowDegreeList(tensor,clr),
            ridx:=[],
            square:=ListWithIdenticalEntries(Order(tensor),0),
            fullrows:=[]);
   return Objectify(NewType(GoodSetsFamily(tensor), IsSymGoodSetCandidate and IsSymGoodSetCandRep), res);
end);


InstallGlobalFunction(EmptyAsymGoodSetCandidate,
function(tensor,brows,bcols)
   local res,nof,clr,h,rf,ml,clrd;

   nof:=NumberOfFibres(tensor);
   h:=GetNormalizingPermutationForAsymCandidate(tensor);
   clr:=Difference([1..OrderOfTensor(tensor)], ReflexiveColors(tensor));
   clr:=Filtered(clr, x->x^Mates(tensor)<>x);
   clr:=Filtered(clr, x->StartBlock(tensor,x) in brows and FinishBlock(tensor,x) in bcols);
   rf:=(Intersection(brows,bcols)<>[]);
   if rf then
      ml:=Length(clr)/2;
   else
      ml:=Length(clr);
   fi;
   res:=rec(tensor:=tensor,
            set:=[],
            nperm:=h,
            nset:=[],
            brows:=Immutable(Set(brows)),
            bcols:=Immutable(Set(bcols)),
            blockingmat:=List([1..nof], a->List([1..nof], b->[])),
            rowdegs:=List([1..nof], x->0),
            coldegs:=List([1..nof], x->0),
            rmaxdeg:=0,
            cmaxdeg:=0,
            ndomain:=OnSets(clr, h),
            maxlength:=ml,
            ndomrowdegs:=RowDegreeList(tensor,clr),
            ndomcoldegs:=ColDegreeList(tensor,clr),
            regflag:=rf,
            ridx:=[],
            cidx:=[],
            square:=ListWithIdenticalEntries(Order(tensor),0),
            fullrows:=[]);
   return Objectify(NewType(GoodSetsFamily(tensor), IsAsymGoodSetCandidate and IsAsymGoodSetCandRep), res);
end);



# input is always a candidate and a normalized color
InstallMethod(ExtendedCandidate,
    "for symmetric candidates in GoodSetCandRep",
    [IsSymGoodSetCandidate and IsGoodSetCandRep, IsPosInt],
function(cand,i)
   local t,h,ci,mates, nd,obj;


   t:=cand!.tensor;
   h:=cand!.nperm;

   if i in cand!.nset then
      return cand;
   fi;
   if not i in cand!.ndomain then
      return fail;
   fi;

   ci:=((i/h)^Mates(t))^h;
   mates:=[i,ci];
   Sort(mates);
   

   nd:=Filtered(cand!.ndomain, k->mates[1]<k and k<>mates[2]);
   mates:=Set(mates);
   
   obj:=rec(tensor:=cand!.tensor,
            set:=Union(cand!.set, OnSets(mates, h^-1)),
            nperm:=h,
            nset:=Union(cand!.nset, mates),
            ndomain:=nd,
            maxlength:=cand!.maxlength);

   return Objectify(NewType(GoodSetsFamily(t), IsSymGoodSetCandidate and IsGoodSetCandRep), obj);
end);

# input is always a candidate and a normalized color
InstallMethod(ExtendedCandidate,
    "for asymmetric candidates in GoodSetCandRep",
    [IsAsymGoodSetCandidate and IsGoodSetCandRep, IsPosInt],
function(cand,i)
   local t,h,ci,nd,obj;

   t:=cand!.tensor;
   h:=cand!.nperm;
   if i in cand!.nset then
      return cand;
   fi;
   if not i in cand!.ndomain then
      return fail;
   fi;

   ci:=((i/h)^Mates(t))^h;

   nd:=Filtered(cand!.ndomain, k->i<k and k<>ci);
   obj:=rec(tensor:=cand!.tensor,
            set:=Union(cand!.set, [i/h]),
            nperm:=h,
            nset:=Union(cand!.nset, [i]),
            ndomain:=nd,
            maxlength:=cand!.maxlength);

   return Objectify(NewType(GoodSetsFamily(t), IsAsymGoodSetCandidate and IsGoodSetCandRep), obj);
end);

InstallMethod(ExtendedCandidate,
    "for symmetric candidates in SymGoodSetCandRep",
    [IsSymGoodSetCandidate and IsSymGoodSetCandRep, IsPosInt],
function(cand,i)
   local t,h,ci,sd,dl,sb,fb,bm,nd,nddl,k,j,obj,rx,sq,md,ck,mates,fr,pos,f;

   t:=cand!.tensor;
   h:=cand!.nperm;
   if i in cand!.nset then
      return cand;
   fi;
   if not i in cand!.ndomain then
      return fail;
   fi;
   ci:=((i/h)^Mates(t))^h;
   if not ci in cand!.ndomain then
      return fail;
   fi;
   mates:=Set([i,ci]);
   sd:=OutValencies(t);
   dl:=ShallowCopy(cand!.degreelist);
   sb:=StartBlock(t,mates[1]/h);
   fb:=FinishBlock(t,mates[1]/h);
   rx:=ShallowCopy(cand!.ridx);
   AddSet(rx,sb);
   AddSet(rx,fb);
   pos:=Position(cand!.blks,sb);
   if pos=fail then
      return fail;
   fi;
   if not fb in cand!.blks then
      return fail;
   fi;
   if cand!.fullrows=[] and pos>1 then
      fr:=cand!.blks{[1..pos-1]};
   else
      fr:=ShallowCopy(cand!.fullrows);
   fi;
   bm:=StructuralCopy(cand!.blockingmat);
   AddSet(bm[sb][fb],mates[1]);
   dl[sb]:=dl[sb]+sd[mates[1]/h];
   md:=Maximum(cand!.maxdeg, dl[sb]);
   if Length(mates)=2 then
      AddSet(bm[fb][sb],mates[2]);
      dl[fb]:=dl[fb]+sd[mates[2]/h];
      md:=Maximum(md, dl[fb]);
   fi;
   if fr<>[] then
      if dl[sb]=dl[fr[1]] then
         AddSet(fr,sb);
      fi;
      if Length(mates)=2 then
        if dl[fb]=dl[fr[1]] then
           AddSet(fr, fb);
        fi;
      fi;
   fi;

   # use blockingmat##############################################################
   sq:=ShallowCopy(cand!.square);                                                #
   for k in [1..Length(sq)] do                                                   #
      sq[k]:=sq[k]+ EntryOfTensor(t, mates[1]/h, (mates[1]/h)^Mates(t), k/h);    #
      for j in cand!.nset do                                                     #
         sq[k]:=sq[k]+EntryOfTensor(t, mates[1]/h,(j/h)^Mates(t),k/h);           #
         sq[k]:=sq[k]+EntryOfTensor(t, j/h,(mates[1]/h)^Mates(t),k/h);           #
      od;                                                                        #
   od;                                                                           #
   if Length(mates)=2 then                                                       #
      for k in [1..Length(sq)] do                                                #
         sq[k]:=sq[k]+ EntryOfTensor(t, mates[2]/h, (mates[2]/h)^Mates(t), k/h); #
         for j in cand!.nset do                                                  #
            sq[k]:=sq[k]+EntryOfTensor(t, mates[2]/h,(j/h)^Mates(t),k/h);        #
            sq[k]:=sq[k]+EntryOfTensor(t, j/h,(mates[2]/h)^Mates(t),k/h);        #
         od;                                                                     #
      od;                                                                        #
   fi;                                                                           #
   ###############################################################################

   nd:=[];
   nddl:=ShallowCopy(cand!.ndomdegreelist);
   for j in [1..Length(cand!.ndomain)] do
      k:=cand!.ndomain[j];
      ck:=((k/h)^Mates(t))^h;
      sb:=StartBlock(t,k/h);
      fb:=FinishBlock(t,k/h);
      f:=true;
      if k<=mates[1] then
         nddl[sb]:=nddl[sb]-sd[k/h];f:=false;
      elif ck<=mates[1] then
         nddl[sb]:=nddl[sb]-sd[k/h];f:=false;
      elif sb in fr then
         nddl[sb]:=nddl[sb]-sd[k/h];f:=false;
      elif fb in fr then
         nddl[sb]:=nddl[sb]-sd[k/h];f:=false;
      elif fr<>[]  then
          if  sd[k/h]+dl[sb]>dl[fr[1]]  then
            nddl[sb]:=nddl[sb]-sd[k/h];f:=false;
          elif sd[ck/h]+dl[fb]>dl[fr[1]] then
            nddl[sb]:=nddl[sb]-sd[k/h];f:=false;
          fi;
      fi;
      if f then
         Add(nd,k);
      fi;
   od;

   obj:=rec(tensor:=cand!.tensor,
            set:=Union(cand!.set, OnSets(mates, h^(-1))),
            nperm:=h,
            nset:=Union(cand!.nset, mates),
            blks:=cand!.blks,
            blockingmat:=bm,
            maxlength:=cand!.maxlength,
            degreelist:=dl,
            maxdeg:=md,
            ndomain:=nd,
            ndomdegreelist:=nddl,
            ridx:=rx,
            square:=sq,
            fullrows:=fr);

   return Objectify(NewType(GoodSetsFamily(t), IsSymGoodSetCandidate and IsSymGoodSetCandRep), obj);
end);




# input is always a candidate and a normalized color
InstallMethod(ExtendedCandidate,
    "for asymmetric candidates in AsymGoodSetCandRep",
    [IsAsymGoodSetCandidate and IsAsymGoodSetCandRep, IsPosInt],
function(cand,i)
   local t,h,sd,rd,cd,sb,pos,fb,ci,nd,ndrd,ndcd,j,k,rx,cx,rf,obj,rm,cm,bm,sq,fr,ck,f;

   t:=cand!.tensor;
   h:=cand!.nperm;
   if i in cand!.nset then
      return cand;
   fi;
   if not i in cand!.ndomain then
      return fail;
   fi;

   sd:=OutValencies(t);
   rd:=ShallowCopy(cand!.rowdegs);
   cd:=ShallowCopy(cand!.coldegs);
   sb:=StartBlock(t,i/h);
   pos:=Position(cand!.brows,sb);
   if pos=fail then
      return fail;
   fi;
   fb:=FinishBlock(t,i/h);
   if not fb in cand!.bcols then
      return fail;
   fi;
   if cand!.fullrows=[] and pos>1 then
      fr:=cand!.brows{[1..pos-1]};
   else
      fr:=ShallowCopy(cand!.fullrows);
   fi;


   bm:=StructuralCopy(cand!.blockingmat);
   AddSet(bm[sb][fb], i);

   rd[sb]:=rd[sb]+sd[i/h];
   rm:=Maximum(rd[sb], cand!.rmaxdeg);
   ci:=((i/h)^Mates(t))^h;
   cd[fb]:=cd[fb]+sd[(i/h)^Mates(t)];
   cm:=Maximum(cd[fb], cand!.cmaxdeg);

   if fr<>[] then
      if rd[sb]=rd[fr[1]] then
         AddSet(fr,sb);
      fi;
   fi;


   # use blockingmat#############################################
   sq:=ShallowCopy(cand!.square);                               #
   for k in [1..Length(sq)] do                                  #
      sq[k]:=sq[k]+ EntryOfTensor(t, i/h, (i/h)^Mates(t), k/h); #
      for j in cand!.nset do                                    #
         sq[k]:=sq[k]+EntryOfTensor(t, i/h,(j/h)^Mates(t),k/h); #
         sq[k]:=sq[k]+EntryOfTensor(t, j/h,(i/h)^Mates(t),k/h); #
      od;                                                       #
   od;                                                          #
   ##############################################################

   nd:=[];
   ndrd:=ShallowCopy(cand!.ndomrowdegs);
   ndcd:=ShallowCopy(cand!.ndomcoldegs);
   for j in [1..Length(cand!.ndomain)] do
      k:=cand!.ndomain[j];
      ck:=((k/h)^Mates(t))^h;
      sb:=StartBlock(t,k/h);
      fb:=FinishBlock(t,k/h);
      f:=true;
      if k<=i then
         ndrd[sb]:=ndrd[sb]-sd[k/h];f:=false;
         ndcd[fb]:=ndcd[fb]-sd[ck/h];
      elif k=ci then
         ndrd[sb]:=ndrd[sb]-sd[k/h];f:=false;
         ndcd[fb]:=ndcd[fb]-sd[ck/h];
      elif sb in fr then
         ndrd[sb]:=ndrd[sb]-sd[k/h];f:=false;
         ndcd[fb]:=ndcd[fb]-sd[ck/h];
      elif fr<>[]  then
         if  sd[k/h]+rd[sb]>rd[fr[1]]  then
            ndrd[sb]:=ndrd[sb]-sd[k/h];f:=false;
            ndcd[fb]:=ndcd[fb]-sd[ck/h];
         elif cand!.regflag and sd[ck/h]+cd[fb]>rd[fr[1]] then
            ndrd[sb]:=ndrd[sb]-sd[k/h];f:=false;
            ndcd[fb]:=ndcd[fb]-sd[ck/h];
         fi;
      fi;
      if f then
         Add(nd,k);
      fi;
   od;

   rx:=ShallowCopy(cand!.ridx);
   AddSet(rx, sb);
   cx:=ShallowCopy(cand!.cidx);
   AddSet(cx, fb);

   obj:=rec(tensor:=cand!.tensor,
            set:=Union(cand!.set, [i/h]),
            nperm:=h,
            nset:=Union(cand!.nset, [i]),
            brows:=cand!.brows,
            bcols:=cand!.bcols,
            blockingmat:=bm,
            maxlength:=cand!.maxlength,
            rowdegs:=rd,
            coldegs:=cd,
            rmaxdeg:=rm,
            cmaxdeg:=cm,
            ndomain:=nd,
            ndomrowdegs:=ndrd,
            ndomcoldegs:=ndcd,
            ridx:=rx,
            cidx:=cx,
            regflag:=cand!.regflag,
            square:=sq,
            fullrows:=fr);
   return Objectify(NewType(GoodSetsFamily(t), IsAsymGoodSetCandidate and IsAsymGoodSetCandRep), obj);
end);


InstallMethod(IsExtendibleCandidate,
    "for candidates in GoodSetCandRep",
    [IsGoodSetCandidate and IsGoodSetCandRep],
function(cand)
   if cand!.ndomain=[] then
      return false;
   fi;

   if Length(cand!.set)>=cand!.maxlength then
      return false;
   fi;

   return true;
end);


InstallMethod(IsExtendibleCandidate,
    "for symmetric candidates in SymGoodSetCandRep",
    [IsSymGoodSetCandidate and IsSymGoodSetCandRep],
function(cand)
   local h,LMab,a,b,subdeg;
   h:=cand!.nperm;
   if cand!.ndomain=[] then
      return false;
   fi;
   if Length(cand!.set)>=cand!.maxlength then
      return false;
   fi;

   if cand!.fullrows<>[] then
      if cand!.maxdeg>cand!.degreelist[cand!.fullrows[1]] then
         return false;
      fi;
   fi;
   if ForAny(cand!.blks, i->cand!.degreelist[i]+cand!.ndomdegreelist[i]<cand!.maxdeg) then
      return false;
   fi;

    LMab:=[];
    for a in cand!.fullrows do
       for b in cand!.fullrows do
          if cand!.blockingmat[a][b]<>[] then
              subdeg:=Set(cand!.square{cand!.blockingmat[a][b]});
              if Length(subdeg)>1 then
                 return false;
              fi;
              UniteSet(LMab, subdeg);
              if Length(LMab)>1 then
                 return false;
              fi;
          fi;
       od;
    od;
    if LMab<>[] then
       for a in cand!.blks do
          for b in cand!.blks do
            if cand!.blockingmat[a][b]<>[] then
               if not a in cand!.fullrows or not b in cand!.fullrows then
                  if Maximum(cand!.square{cand!.blockingmat[a][b]})>LMab[1] then
                     return false;
                  fi;
               fi;
            fi;
          od;
       od;
    fi;
   return true;
end);


InstallMethod(IsExtendibleCandidate,
    "for asymmetric candidates in AsymGoodSetCandRep",
    [IsAsymGoodSetCandidate and IsAsymGoodSetCandRep],
function(cand)
   local rmax,cmax,ridx,cidx,rdl,cdl,rdl2,cdl2,LMab,a,b,idx,M1,M2,MM,subdeg,h;

   h:=cand!.nperm;
   if cand!.ndomain=[] then
      return false;
   fi;

   if Length(cand!.set)>=cand!.maxlength then  # was 2* but this is a mistake
      return false;
   fi;

   rmax:=cand!.rmaxdeg;
   cmax:=cand!.cmaxdeg;
   ridx:=cand!.ridx;
   cidx:=cand!.cidx;

   if cand!.regflag then
      if cand!.fullrows<>[] then
         if cmax>rmax then
            return false;
         fi;
      fi;
      cmax:=rmax;
      ridx:=Union(ridx,cidx);
      cidx:=ridx;
   fi;
   if cand!.fullrows<>[] then
      if cand!.rowdegs[cand!.fullrows[1]]<rmax then
         return false;
      fi;
      if rmax>cand!.rowdegs[cand!.fullrows[1]] then
         return false;
      fi;
   fi;

   if ForAny(cand!.brows, i->cand!.rowdegs[i]+cand!.ndomrowdegs[i]<rmax) then
      return false;
   fi;
   if ForAny(cand!.bcols, i->cand!.coldegs[i]+cand!.ndomcoldegs[i]<cmax) then
      return false;
   fi;

    LMab:=[];
    for a in cand!.fullrows do
       for b in cand!.fullrows do
          if cand!.blockingmat[a][b]<>[] then
              subdeg:=Set(cand!.square{cand!.blockingmat[a][b]});
              if Length(subdeg)>1 then
                 return false;
              fi;
              UniteSet(LMab, subdeg);
              if Length(LMab)>1 then
                 return false;
              fi;
          fi;
       od;
    od;
    if LMab<>[] and cand!.regflag then
       for a in [1..NumberOfFibres(cand!.tensor)] do
          for b in [1..NumberOfFibres(cand!.tensor)] do
            if cand!.blockingmat[a][b]<>[] then
               if not a in cand!.fullrows or not b in cand!.fullrows then
                  if Maximum(cand!.square{cand!.blockingmat[a][b]})>LMab[1] then
                     return false;
                  fi;
               fi;
            fi;
          od;
       od;
    fi;

   return true;
end);

InstallMethod(NormalizedDomainOfCandidate,
    "for good set candidates",
    [IsGoodSetCandidate and IsGoodSetCandRep],
function(cand)
     return cand!.ndomain;
end);

InstallMethod(NormalizedDomainOfCandidate,
    "for asymmetric candidates in AsymGoodSetCandRep",
    [IsAsymGoodSetCandidate and IsAsymGoodSetCandRep],
function(cand)
  local h,nd,rb;

  if cand!.fullrows=[] then
     return cand!.ndomain;
  fi;

  h:=cand!.nperm;
  nd:=cand!.ndomain;
  rb:=First(cand!.brows, x->not (x in cand!.fullrows));
  if rb=fail then
     return [];
  fi;
  nd:=Filtered(nd, x->StartBlock(cand!.tensor, x/h)=rb);

  return nd;

end);

InstallMethod(NormalizedDomainOfCandidate,
    "for symmetric candidates in SymGoodSetCandRep",
    [IsSymGoodSetCandidate and IsSymGoodSetCandRep],
function(cand)
  local h,nd,rb;

  if cand!.fullrows=[] then
     return cand!.ndomain;
  fi;
  h:=cand!.nperm;
  nd:=cand!.ndomain;
  rb:=First(cand!.blks, x->not (x in cand!.fullrows));
  if rb=fail then
     return [];
  fi;
  nd:=Filtered(nd, x->StartBlock(cand!.tensor, x/h)=rb or FinishBlock(cand!.tensor, x/h)=rb);

  return nd;
end);

InstallMethod(NormalizedSetOfCandidate,
    "for good set candidates",
    [IsGoodSetCandidate and IsGoodSetCandRep],
function(cand)
  return cand!.nset;
end);


InstallMethod(SetOfCandidate,
    "for good set candidates",
    [IsGoodSetCandidate and IsGoodSetCandRep],
function(cand)
  return cand!.set;
end);

InstallMethod(TensorOfCandidate,
    "for good set candidates",
    [IsGoodSetCandidate and IsGoodSetCandRep],
function(cand)
  return cand!.tensor;
end);

InstallMethod(TestCandidate,
    "for asymmetric candidates",
    [IsAsymGoodSetCandidate],
function(cand)
    local T,part,gs,res,set;

    T:=TensorOfCandidate(cand);
    res:=[];
    set:=SetOfCandidate(cand);
    gs:=[set, OnSets(set, Mates(T))];
    part:=WLBuildAsymGoodSetPartition(T,gs);
    part:=WLStabil(T,part);
    if part <>false then
        res:=[gs,part];
    fi;

    return res;
end);

InstallMethod(TestCandidate,
    "for symmetric candidates",
    [IsSymGoodSetCandidate],
function(cand)
    local T,part,gs,res;

    T:=TensorOfCandidate(cand);
    res:=[];
    gs:=SetOfCandidate(cand);
    part:=WLBuildSymGoodSetPartition(T,gs);
    part:=WLStabil(T,part);
    if part<> false then
        res:=[[gs],part];
    fi;

    return res;
end);


InstallMethod(TestCandidate,
    "for asymmetric candidates in AsymGoodSetCandRep",
    [IsAsymGoodSetCandidate and IsAsymGoodSetCandRep],
function(cand)
    local T,part,gs,res;
    if Length(Set(cand!.rowdegs{cand!.brows}))<>1 then
       return [];
    fi;

    if Length(Set(cand!.coldegs{cand!.bcols}))<>1 then
       return [];
    fi;

    if (cand!.regflag) and cand!.rowdegs[cand!.brows[1]]<>cand!.coldegs[cand!.bcols[1]] then
       return [];
    fi;

    T:=cand!.tensor;
    res:=[];
    gs:=[cand!.set, OnSets(cand!.set, Mates(T))];
    part:=WLBuildAsymGoodSetPartition(T,gs);
    part:=WLStabil(T,part);
    if part <>false then
        res:=[gs,part];
    fi;

    return res;
end);

InstallMethod(TestCandidate,
    "for symmetric candidates in SymGoodSetCandRep",
    [IsSymGoodSetCandidate and IsSymGoodSetCandRep],
function(cand)
    local T,part,gs,res;
    if Length(Set(cand!.degreelist{cand!.blks}))<>1 then
       return [];
    fi;


    T:=cand!.tensor;
    res:=[];
    gs:=cand!.set;
    part:=WLBuildSymGoodSetPartition(T,gs);
    part:=WLStabil(T,part);
    if part<> false then
        res:=[[gs],part];
    fi;

    return res;
end);



InstallGlobalFunction(ExtendAsymGSCand,
function(S,SM, cand)
    local dom,res,orbits,M,i,SC,ncand,part;

    dom:=NormalizedDomainOfCandidate(cand);
    res:=[];
    orbits:=StbcOrbits(SM, dom);
    orbits:=Intersection(dom,Set(orbits,Minimum));
    M:=NormalizedSetOfCandidate(cand);

    for i in orbits do
        SC:=CocoSetReducibilityTest(S,SM,M,i);
        if not IsPerm(SC) then
            ncand:=ExtendedCandidate(cand,i);
            
            part:=TestCandidate(ncand);
            if part<>[] then
                Add(res, [SC,part[1],part[2].classes]);
                COCOPrint(",\c");
            fi;
            
            if IsExtendibleCandidate(ncand) then
                Append(res, ExtendAsymGSCand(S, SC, ncand));
            fi;
        fi;
    od;
    return res;
end);

InstallMethod(NormalizingPermutationOfCandidate,
        "for all good set candidates in GoodSetCandRep",
        [IsGoodSetCandidate and IsGoodSetCandRep],
function(cand)
    return cand!.nperm;
end);


InstallGlobalFunction(ExtendSymGSCand,
function(S,SM, cand)
    local dom,res,orbits,M,i,mates,ncand,part,SC,h,T;

    T:=TensorOfCandidate(cand);
    h:=NormalizingPermutationOfCandidate(cand);
    dom:=NormalizedDomainOfCandidate(cand);
    res:=[];
    orbits:=StbcOrbits(SM, dom);
    orbits:=Intersection(Set(orbits,Minimum),dom);

    orbits:=Filtered(orbits, x->((x/h)^Mates(T))^h >= x);
    M:=NormalizedSetOfCandidate(cand);
    
    for i in orbits do
        mates:=Set([i,((i/h)^Mates(T))^h]);
        SC:=CocoSetReducibilityTest(S,SM,M,mates[1]);
        if not IsPerm(SC) then
          if Length(mates)=2 then
            SC:=CocoSetReducibilityTest(S,SC,Union(M,[mates[1]]),mates[2]);
          fi;
        fi;

        if not IsPerm(SC)  then
            ncand:=ExtendedCandidate(cand,mates[1]);
            part:=TestCandidate(ncand);
            if part<>[] then
                Add(res,[SC,part[1],part[2].classes]);
                COCOPrint(".\c");
            fi;
            if IsExtendibleCandidate(ncand) then
                Append(res, ExtendSymGSCand(S, SC, ncand));
            fi;
        fi;
    od;
    return res;
end);

InstallGlobalFunction(SUBHomAsymGSReps,
function(GT,T)
    local h,G,S,cand,dom,firsts,result,i,Si,part,ncand;

    if IsHomogeneous(T) then
        cand:=EmptyAsymGoodSetCandHom(T);
    else
        cand:=EmptyAsymGoodSetCandidate(T,[1..NumberOfFibres(T)], [1..NumberOfFibres(T)]);
    fi;
    
    h:=NormalizingPermutationOfCandidate(cand);
    G:=GT^h;
    S:=Stbc(G);
    
    dom:=NormalizedDomainOfCandidate(cand);
    firsts:=StbcMinimalOrbitReps(S,dom);
    firsts:=Filtered(firsts, x->x<((x/h)^Mates(T))^h);
 #   Error("test1");
    
    result:=[];
    for i in firsts do
        ncand:=ExtendedCandidate(cand,i);
        Si:=StbcStabilizer(S,i);
        
        part:=TestCandidate(ncand);
        
        if part<>[] then
            COCOPrint(",\c");
            Add(result, [StbcGroup(Si)^(h^-1),part[1],part[2].classes]);
        fi;
        
        Append(result, List(ExtendAsymGSCand(S,Si,ncand), x->[StbcGroup(x[1])^(h^-1), x[2], x[3]]));
    od;
    return result;
end);

InstallGlobalFunction(SUBHomSymGSReps,
function(GT,T)
    local h,G, S,cand,reps;


    if IsHomogeneous(T) then
        cand:=EmptySymGoodSetCandHom(T);
    else
        cand:=EmptySymGoodSetCandidate(T,[1..NumberOfFibres(T)]);
    fi;
    h:=NormalizingPermutationOfCandidate(cand);
    G:=GT^h;
    S:=Stbc(G);

    reps:=ExtendSymGSCand(S, StbcCopy(S), cand);
    reps:=List(reps, x->[StbcGroup(x[1])^(h^-1), x[2], x[3]]); 
    
    return reps;
end);


########################################################################################

DeclareRepresentation("IsGoodSetRep",
        IsAttributeStoringRep,
        [ "tensor",             # the tensor over which the good set "lives"
          "set",                # the good set of colors of <tensor>
          "part",               # the WL-stable partition induced by <set>
        ]);

InstallGlobalFunction(BuildGoodSet,
function(arg)
   local tensor,set,part,res;
   
   tensor:=arg[1];
   set:=arg[2];
   if Length(arg)=3 then
       part:=arg[3];
   else
       part:=WLBuildSymGoodSetPartition(tensor,set);
       part:=WLStabil(tensor,part);
       if part=false then
           return fail;
       fi;
       part:=part.classes;
   fi;
   

   res:=rec(
            tensor:=tensor,
            set:=Immutable(set),
            part:=Immutable(part));
   return Objectify(NewType(GoodSetsFamily(tensor), IsGoodSet and IsGoodSetRep), res);
end);

InstallMethod(TensorOfGoodSet,
        "for good sets in GoodSetRep",
        [IsGoodSet and IsGoodSetRep],
function(gs)
   return gs!.tensor;
end);

InstallOtherMethod(AsSet,
        "for good sets in GoodSetRep",
        [IsGoodSet and IsGoodSetRep],
function(gs)
  return gs!.set;
end);

InstallOtherMethod(Length,
        "for good sets",
        [IsGoodSet],
function(gs)
    return Length(AsSet(gs));
end);

InstallOtherMethod(\<,
        "for good sets",
        IsIdenticalObj,
        [IsGoodSet,IsGoodSet],
function(gs1,gs2)
    if Length(gs1)<>Length(gs2) then
        return Length(gs1)<Length(gs2);
    else
        return AsSet(gs1)<AsSet(gs2);
    fi;
end);

InstallOtherMethod(\=,
        "for good sets",
        IsIdenticalObj,
        [IsGoodSet,IsGoodSet],
function(gs1,gs2)
    return AsSet(gs1)=AsSet(gs2);
end);

    
# <g> must be from Aut(<gs!.tensor>)
InstallMethod(OnGoodSets,
        "for good sets in GoodSetRep",
        [IsGoodSet and IsGoodSetRep, IsPerm],
function(gs, g)
    local res;
   res:=rec(
            tensor:=gs!.tensor,
            set:=MakeImmutable(OnSets(gs!.set,g)),
            part:=MakeImmutable(OnSetsSets(gs!.part,g)));
   return Objectify(NewType(GoodSetsFamily(gs!.tensor), IsGoodSet and IsGoodSetRep), res);
end);

InstallMethod(PartitionOfGoodSet,
        "for good sets in GoodSetRep",
        [IsGoodSet and IsGoodSetRep],
function(gs)
    return gs!.part;
end);




#################################################################
#M  ViewObject( <GoodSet> )
##
InstallMethod(ViewObj,
        "for good set orbits",
        [IsGoodSet],
        function(x) local s,t;
    
    t:=TensorOfGoodSet(x);
    s:=AsSet(x);
    
    Print("<");
    if IsMutable(x) then
        Print("mutable ");
    fi;
    if s<>[] and not s[1]^Mates(t) in s then
        Print("antisymmetric ");
    else
        Print("symmetric ");
    fi;
    
    Print("GoodSet ", s, ">");
end);


##########################################################################################



    


# GoodSetOrbit(<group>, <gs> [,<stab>])
# <stab> is supposed to be a subgroup of the stabilizer of <gs> in <group>
InstallGlobalFunction(GoodSetOrbit,
function(arg)
    local group,gs,stab, can,xstab,nstab;
    
    group:=arg[1];
    gs:=arg[2];
    if Length(arg)=2 then
        stab:=Stabilizer(group,AsSet(gs), OnSets);
    else
        stab:=arg[3];
    fi;
    
    can:=SetCanonifiers(Stbc(group), Stbc(stab), AsSet(gs));
    nstab:=ClosureGroup(stab, List(can, x->can[1]*x^(-1)));
    
    
    return GoodSetOrbitNC(group, OnGoodSets(gs,can[1]), nstab^can[1]);
end);




# GoodSetOrbitNC(<group>, <gs> [,<stab>])
# <gs> is a good set that is assumed to be minimal (lexicographically) in its orbit
# the minimality property is not checked
# <stab> is supposed to be the full (good-set-wise) stabilizer of <gs> in <group> 
InstallGlobalFunction(GoodSetOrbitNC,
function(arg)
    local group,gs,stab,res;
    
    group:=arg[1];
    gs:=arg[2];
    if Length(arg)=2 then
        stab:=Stabilizer(group,AsSet(gs), OnSets);
    else
        stab:=arg[3];
    fi;
    
    res:=rec(
            group:=group,
            rep:=gs,
            stab:=stab);
   return Objectify(NewType(GoodSetOrbitFamily(TensorOfGoodSet(gs),group), IsGoodSetOrbit and IsCocoOrbitRep), res);
end);



InstallMethod(OnCocoOrbits,
        "for all good set orbits",
        [IsGoodSetOrbit, IsPerm],
function(gsorb,perm)
    local   grp,  gs,  stab,  ngs,  ngrp,  nstab;
    
    grp:=UnderlyingGroupOfCocoOrbit(gsorb);
    gs:=CanonicalRepresentativeOfCocoOrbit(gsorb);
    stab:=StabilizerOfCanonicalRepresentative(gsorb);
    
    ngs:=OnGoodSets(gs,perm);
#    ngrp:=grp^perm;
#    nstab:=stab^perm;
    return GoodSetOrbit(grp,ngs,Stabilizer(grp,AsSet(ngs),OnTuples),FamilyObj(gsorb));
end);

    
    
InstallMethod(SubOrbitsOfCocoOrbit,
        "for all set orbits",
        [IsPermGroup, IsGoodSetOrbit],
function(grp,gsorb)
    local   ug,  cosreps,  stab,  gs,  ngs;

    
    ug:=UnderlyingGroupOfCocoOrbit(gsorb);
    
    if not IsSubgroup(ug,grp) then
        Error("SubOrbitsOfGoodSetOrbit: The given group is not a subgroup of the underlying group of the good set orbit!");
    fi;
    cosreps:=List(RightCosetsNC(ug,grp), x->Representative(x)^(-1)); # get left-coset representatives
    stab:=StabilizerOfCanonicalRepresentative(gsorb);
    gs:=CanonicalRepresentativeOfCocoOrbit(gsorb);
    ngs:=GoodSetOrbitNC(grp,gs, Intersection(stab,grp));
    
    return List(cosreps, x->OnCocoOrbits(ngs,x));
end);

InstallMethod(SubOrbitsWithInvariantPropertyOfCocoOrbit,
        "for good set orbits",
        [IsPermGroup, IsGoodSetOrbit, IsFunction],
function(grp,gsorb,func)
    local   ug,  cosreps,  stab,  gs,  ngs,  res;
    #,testgsorb,testorbreps;

    ug:=UnderlyingGroupOfCocoOrbit(gsorb);
    
    if not IsSubgroup(ug,grp) then
        Error("SubOrbitsOfGoodSetOrbit: The given group is not a subgroup of the underlying group of the good set orbit!");
    fi;
    # testgsorb:=AsSet(gsorb);
    # testorbreps:=Set(Orbits(grp,testgsorb,OnGoodSets),Minimum);
    # testorbreps:=Filtered(testorbreps,func);
        
    cosreps:=List(RightCosetsNC(ug,grp), x->Representative(x)^(-1)); # get left-coset representatives
    stab:=StabilizerOfCanonicalRepresentative(gsorb);
    gs:=CanonicalRepresentativeOfCocoOrbit(gsorb);
    ngs:=GoodSetOrbitNC(grp,gs, Intersection(stab,grp));
#    cosreps:=Filtered(cosreps, r->func(OnGoodSets(CanonicalRepresentativeOfCocoOrbit(ngs),r)));
    res:=List(cosreps, x->OnCocoOrbits(ngs,x));
    res:=Filtered(res, x->func(CanonicalRepresentativeOfCocoOrbit(x)));
    
    # if Length(Set(res))<>Length(testorbreps) then
    #     Error("Error in SubOrbitsOfGoodSetOrbit!");
    # fi;
    
    return Set(res);
end);
   


# InstallMethod(CocoOrbitFamily,
#         "for good set orbits",
#         [IsGoodSetOrbit],
# function(gso)
#     return NewFamily("GoodSetOrbitFam", IsGoodSetOrbit);
# end);


InstallMethod(HomogeneousGoodSetOrbits,
        "for structure constants tensors",
        [IsTensor and IsTensorOfCC],
function(T)
    local aaut;
    aaut:=AutGroupOfCocoObject(T);
    return HomogeneousGoodSetOrbits(aaut,T);
end);

InstallOtherMethod(HomogeneousGoodSetOrbits,
        "for structure constants tensors",
        [IsPermGroup, IsTensor and IsTensorOfCC],
function(G,T)
    local   ags,  sgs,  lgs;
    
    if not ForAll(GeneratorsOfGroup(G), g->IsAutomorphismOfObject(T,g)) then
        Error("AllGoodSetOrbitsOfTensor: Given group mut preserve the tensor of structure-constants!");
        return fail;
    fi;
    ags:=SUBHomAsymGSReps(G,T);
    ags:=Union(List([1,2], i->  List(ags, gs->GoodSetOrbit(G,BuildGoodSet(T,gs[2][i],gs[3]),gs[1]))));
    sgs:=SUBHomSymGSReps(G,T);
    sgs:=Set(sgs, gs->GoodSetOrbit(G, BuildGoodSet(T,gs[2][1],gs[3]), gs[1]));
    lgs:=Union(ags,sgs);
    return lgs;
end);


InstallOtherMethod(HomogeneousGoodSetOrbits,
        "for structure constants tensors",
        [IsPermGroup, IsTensor and IsTensorOfCC, IsString],
function(G,T,mode)
    local   ags,  sgs,  lgs;
    
    if not ForAll(GeneratorsOfGroup(G), g->IsAutomorphismOfObject(T,g)) then
        Error("AllGoodSetOrbitsOfTensor: Given group must preserve the tensor of structure-constants!");
        return fail;
    fi;
    lgs:=[];
    
    if 'a' in mode then
        ags:=SUBHomAsymGSReps(G,T);
        lgs:=Union(List([1,2], i->  List(ags, gs->GoodSetOrbit(G,BuildGoodSet(T,gs[2][i],gs[3]),gs[1]))));
    fi;
    if 's' in mode then
        sgs:=SUBHomSymGSReps(G,T);
        lgs:=Union(lgs,Set(sgs, gs->GoodSetOrbit(G, BuildGoodSet(T,gs[2][1],gs[3]), gs[1])));
    fi;
    
    return lgs;
end);
         
InstallMethod(ActionOfCocoOrbit,
        "for all fusion orbits",
        [IsGoodSetOrbit],
function(orb)
    return OnGoodSets;
end);


#################################################################
#M  ViewObject( <GoodSetOrbit> )
##
InstallMethod(ViewObj,
        "for good set orbits",
        [IsGoodSetOrbit],
        function(x)
    Print("<");
    if IsMutable(x) then
        Print("mutable ");
    fi;
    Print("GoodSetOrbit of length ", Size(x), ">");
end);

