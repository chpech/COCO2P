InstallGlobalFunction(ExtendSetOrbitRepCand,
function(cand)
    local   dom,  res,  i,  ncand,  orbit;

    dom:=DomainOfSetOrbitRepCand(cand);
    res:=[];

    for i in dom do
        ncand:=ExtendedSetOrbitRepCand(cand,i);
        if ncand=fail then
            continue;
        fi;


        orbit:=TestSetOrbitRepCand(ncand);
        if part<>fail then
            Add(res,  orbit);
            Print(",\c");
        fi;

        if IsExtendibleSetOrbitRepCand(ncand) then
            Append(res, ExtendSetOrbitRepCand(ncand));
        fi;
    od;
    return res;
end);

DeclareRepresentative("IsSetOrbitRepCandRep",
        IsAttributeStoringRep,
        [ "set",
          "domain",
          "maxlength",
          "grpS",
          "stabS",
          ]);

DeclareRepresentation("IsAsymGoodSetOrbitRepCandRep",
        IsSetOrbitRepCandRep,
        [ "set",                # the normalized candidate
          "domain",             # the normalized domain
          "maxlength",          # the maximal length of a good set
          "grpS",               # stabilizer chain of the normalized group
          "stabS",              # stabchain of the stabilizer of <set> in grpS
          "grp",                # the (non normalized) group
          "tensor",             # the tensor over which the candidate "lives"
          "cset",               # a subset of colors of <tensor> (corresponding to <set>)
          "nperm",              # the normalizing permutation
          "bcols",              # the block-columns to which colors from <cset> have to belong
          "brows",              # the block rows to which colors from <cset> have to belong
          "blockingmat",        # the blocking-matrix of the colors from <cset>
          "rowdegs",            # for each block the out-valency of the set in this block
          "coldegs",            #
          "rmaxdeg",            # the maximum of rowdegs
          "cmaxdeg",            # the maximum of coldegs
          "domrowdegs",         # the RowDegreeList of domain
          "domcoldegs",         # the ColDegreeList of domain
          "ridx",               # block rows from which colors have been chosen
          "cidx",               # block columns from which colors have been chosen
          "regflag",            # true if we are searching for a regular asym. good set
          "square",             # cset * cset^Mates(tensor) (in normalized order)
          "fullrows"            # block rows that are already full
        ]);

InstallGlobalFunction(EmptyAsymGoodSetOrbitRepCand,
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
   res:=rec(
            set:=[],
            domain:=OnSets(clr, h),
            maxlength:=ml,
            tensor:=tensor,
            cset:=[],
            nperm:=h,
            bcols:=Immutable(Set(bcols)),
            brows:=Immutable(Set(brows)),
            blockingmat:=List([1..nof], a->List([1..nof], b->[])),
            rowdegs:=List([1..nof], x->0),
            coldegs:=List([1..nof], x->0),
            rmaxdeg:=0,
            cmaxdeg:=0,
            domrowdegs:=RowDegreeList(tensor,clr),
            domcoldegs:=ColDegreeList(tensor,clr),
            ridx:=[],
            cidx:=[],
            regflag:=rf,
            square:=ListWithIdenticalEntries(Order(tensor),0),
            fullrows:=[]);
   return Objectify(NewType(GoodSetsFamily(tensor), IsAsymGoodSetOrbitRepCandidate and IsAsymGoodSetOrbitRepCandRep), res);
end);

# input is always a candidate and a normalized color
InstallMethod(ExtendedSetOrbitRep,
    "for asymmetric candidates in AsymGoodSetCandRep",
    [IsAsymGoodSetOrbitRepCandidate and IsAsymGoodSetOrbitRepCandRep, IsPosInt],
function(cand,i)
   local t,h,sd,rd,cd,sb,pos,fb,ci,nd,ndrd,ndcd,j,k,rx,cx,rf,obj,rm,cm,bm,sq,fr,ck,f;

   t:=cand!.tensor;
   h:=cand!.nperm;
   if i in cand!.set then
      return cand;
   fi;
   if not i in cand!.domain then
      return fail;
   fi;
   nstabS:=CocoSetReducibilityTest(cand!.grpS, cand!.stabS, cand!.set,i);
   if nstabS=fail then
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
   ndrd:=ShallowCopy(cand!.domrowdegs);
   ndcd:=ShallowCopy(cand!.domcoldegs);
   for j in [1..Length(cand!.domain)] do
      k:=cand!.domain[j];
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

   obj:=rec(
            set:=Union(cand!.nset, [i]),
            domain:=nd,
            maxlength:=cand!.maxlength,
            grpS:=cand!.grpS,
            stabS:=nstabS,
            grp:=cand!.grp,
            tensor:=cand!.tensor,
            cset:=Union(cand!.set, [i/h]),
            nperm:=h,
            bcols:=cand!.bcols,
            brows:=cand!.brows,
            blockingmat:=bm,
            rowdegs:=rd,
            coldegs:=cd,
            rmaxdeg:=rm,
            cmaxdeg:=cm,
            domrowdegs:=ndrd,
            domcoldegs:=ndcd,
            ridx:=rx,
            cidx:=cx,
            regflag:=cand!.regflag,
            square:=sq,
            fullrows:=fr);
   return Objectify(NewType(GoodSetsFamily(t), IsAsymGoodSetOrbitRepCandidate and IsAsymGoodSetOrbitRepCandRep), obj);
end);

InstallMethod(IsExtendibleSetOrbitRepresentative,
    "for asymmetric candidates in AsymGoodSetCandRep",
    [IsAsymGoodSetOrbitRepCandidate and IsAsymGoodSetOrbitRepCandRep],
function(cand)
   local rmax,cmax,ridx,cidx,rdl,cdl,rdl2,cdl2,LMab,a,b,idx,M1,M2,MM,subdeg,h;

   h:=cand!.nperm;
   if cand!.domain=[] then
      return false;
   fi;

   if Length(cand!.set)>=cand!.maxlength then
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

   if ForAny(cand!.brows, i->cand!.rowdegs[i]+cand!.domrowdegs[i]<rmax) then
      return false;
   fi;
   if ForAny(cand!.bcols, i->cand!.coldegs[i]+cand!.domcoldegs[i]<cmax) then
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

InstallMethod(DomainOfSetOrbitRepCand,
    "for asymmetric candidates in AsymGoodSetCandRep",
    [IsAsymGoodSetOrbitRepCandidate and IsAsymGoodSetOrbitRepCandRep],
function(cand)
    local h,rb,dom;

    if cand!.fullrows=[] then
        dom:=cand!.domain;
    else

        h:=cand!.nperm;
        nd:=cand!.domain;
        rb:=First(cand!.brows, x->not (x in cand!.fullrows));
        if rb=fail then
            return [];
        fi;
        dom:=Filtered(nd, x->StartBlock(cand!.tensor, x/h)=rb);
    fi;
    orbreps:=Set(StbcOrbits(cand!.stabS,dom),Minimum);
    return Intersection(dom, orbreps);
end);

InstallMethod(TestSetOrbitRepCand,
    "for asymmetric candidates in AsymGoodSetCandRep",
    [AsymGoodSetOrbitRepCandidate and IsAsymGoodSetOrbitRepCandRep],
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
    gs:=[cand!.cset, OnSets(cand!.cset, Mates(T))];
    part:=WLBuildAsymGoodSetPartition(T,gs);
    part:=WLStabil(T,part);
    if part <>fail then
        h:=cand!.nperm;
        stab:=StbcGroup(cand!.stabS)^(h^-1)
        return GoodSetOrbit(cand!.grp,BuildGoodSet(T, cand!.cset,part.classes),stab);
    else
        return fail;
    fi;
end);
