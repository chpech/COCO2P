#############################################################################
##
##  redtest.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of the irreducibility test for set-orbit representatives
##  and for set-set-orbit representatives
## 
#############################################################################


# xS: The stabilizer chain of a group
# M: a set of points
# SM: a stabilizer chain of the set-stabilizer of M in xS
# x a point not in M
# the function searches breadth first for an element h of xS that OnSets(Union(M,[x]),h)< Union(M,[x])
# if such an element exists, then it is returned
# otherwise a stabilizer chain of the set-stabilizer of Union(M,[x]) in Sx is returned
#
# the program uses internally candidates for partial reductions (these are the nodes of the search tree)
# a candidate is a list  [SoN,N,g] where
# N is a set (some  initial segment coincides with M)
# SoN is the stabilizer chain of a subgroup of the stabilizer of M in xS
# OnSets(M,g)=N
# which subgroup SoN describes depends on lev
InstallGlobalFunction(CocoSetReducibilityTest,
function(xS,SM,M,x)
   local S, len, MM, sMM, xSM, newSM,max,cands,lev,newcands, minOrbRepsS,c,orN,minoy,h,newSoN,newN,OI,y,m;

   if xS.generators=[] then
      return CopyStabChain(SM);
   fi;
   S:=CopyStabChain(xS);
   len:=Length(M)+1;
   MM:=Concatenation([x],M);
   sMM:=Set(MM);
   ChangeStabChain(S,sMM);
   xSM:=SM;
   xSM:=StbcStabilizer(xSM,x);
   newSM:=CopyStabChain(xSM);
   InsertTrivialStabilizer(newSM,x);
   if M<>[] then
      m:=Maximum(M);
   else
      m:=0;
   fi;
   max:=Maximum(x,StbcMaximumMovedPoint(S),m);
   cands:=[[xSM,sMM,()]];
   for lev in [1..len] do
     newcands:=[];
     if S.generators=[] then
       cands:=Filtered(cands, x->x[2]{[lev..len]}=sMM{[lev..len]} and x[3]<>());
       cands:=List(cands, x->x[3]);
       AddGeneratorsExtendSchreierTree(newSM,cands);
       return newSM;
     fi;
     OI:=StbcEmptyOrbitInformation(S,max);
     for c in cands do
       if c[1].generators<>[] then
         orN:=StbcMinimalOrbitRepsCon(c[1],c[2]{[lev..len]},c[3]);
       else
         orN:=c[2]{[lev..len]};
       fi;
       for y in orN do
         if not OI[3][y] then
            ExtendOrbitInformation(OI,y);
         fi;
         minoy:=OI[4][y];
         if minoy<sMM[lev] then
             ChangeStabChain(S,[minoy]);
             h:=InverseRepresentative(S,y);
             return c[3]*h;
         fi;
         if minoy=sMM[lev] then
           if S.orbit[1]=sMM[lev] then
             h:=InverseRepresentative(S,y);
           else
             h:=();
           fi;
           newSoN:=CopyStabChain(c[1]);
           newSoN:=StbcStabilizer(newSoN,y/c[3]);
           newN:=OnSets(c[2],h);
           if newN{[lev+1..len]}<sMM{[lev+1..len]} then
             return c[3]*h;
           fi;
           Add(newcands,[newSoN,newN,c[3]*h]);
         fi;
       od;
     od;
     cands:=newcands;
#     COCOPrint(Length(cands),"\n");

     if S.orbit[1]=sMM[lev] then
       S:=S.stabilizer;
     fi;
   od;
   cands:=Filtered(cands, x->x[3]<>());
   cands:=List(cands, x->x[3]);
   AddGeneratorsExtendSchreierTree(newSM,cands);
   return newSM;
end);

InstallGlobalFunction(CocoTwoSetOrbitRepresentatives,
function(G, n)
    local  res, S, dom, firsts, i, Si, seconds, j, SC;

    res:=[];

    S:=Stbc(G);
    dom:=[1..n];
    firsts:=StbcMinimalOrbitReps(S,dom);
    for i in firsts do
        Si:=StbcStabilizer(S,i);
        seconds:=StbcMinimalOrbitReps(Si,[i+1..n]);
        for j in seconds do
            SC:=CocoSetReducibilityTest(S,Si,[i],j);
            if not IsPerm(SC) then
                Add(res,[i,j]);
            fi;
        od;
    od;
    return res;
end);


# SetStabilizerStabChainOfCurrentSetOrbitRep:=function(sor)
#     local iter;

#     if not IsBound(sor!.iterator) then
#         Error("There is no current set orbit representative (no iterator)!");
#     fi;
#     iter:=sor!.iterator;
#     if iter!.depth=0 then
#         Error("There is no current set orbit representative (iterator not active)!");
#     fi;

#     return StbcCopy(iter!.stack[iter!.depth].stabilizer);
# end;


SetCanonifiers:=function(xS,SM,M)
    local   S,len,  m,  max,  cM,  cands,  lev,  newcands,  minSet,  c,
            cosReps,  OI,  orN,  y,  minoy,  h,  newSoN,  newN;

    if xS.generators=[] then
        return [()];
    fi;
    S:=CopyStabChain(xS);

    len:=Length(M);  #   len:=Length(M)+1;
    ChangeStabChain(S,M);
    if M<>[] then
        m:=Maximum(M);
    else
        m:=0;
    fi;
    max:=Maximum(StbcMaximumMovedPoint(S),m);


    cM:=[];

    cands:=[[SM,M,()]];
    for lev in [1..len] do
        newcands:=[];
        if S.generators=[] then
            minSet:=M;
            cosReps:=[];
            for c in cands do
                if c[2]<minSet then
                    minSet:=c[2];
                    cosReps:=[c[3]];
                elif c[2]=minSet then
                    AddSet(cosReps, c[3]);
                fi;
            od;

            return cosReps;
        fi;
        OI:=StbcEmptyOrbitInformation(S,max);
        for c in cands do
            if c[1].generators<>[] then
                orN:=StbcMinimalOrbitRepsCon(c[1],c[2]{[lev..len]},c[3]);
            else
                orN:=c[2]{[lev..len]};
            fi;
            for y in orN do
                if not OI[3][y] then
                    ExtendOrbitInformation(OI,y);
                fi;
                minoy:=OI[4][y];
                if not IsBound(cM[lev]) then
                    cM[lev]:=minoy;
                fi;

                if minoy<=cM[lev] then
                    if minoy<cM[lev] then
                        cM[lev]:=minoy;
                    fi;

                    ChangeStabChain(S,[minoy]);
                    if S.orbit[1]=cM[lev] then
                        h:=InverseRepresentative(S,y);
                    else
                        h:=();
                    fi;
                    newSoN:=CopyStabChain(c[1]);
                    newSoN:=StbcStabilizer(newSoN,y/c[3]);
                    newN:=OnSets(c[2],h);

                    Add(newcands,[newSoN,newN,c[3]*h]);
                fi;
            od;
        od;

        cands:=Filtered(newcands, x->x[2][lev]= cM[lev]);

        if S.orbit[1]=cM[lev] then
            S:=S.stabilizer;
        fi;
    od;

    cosReps:=Set(cands, x->x[3]);

    return cosReps;
end;

IsCanonicalSetOrbitRep:=function(xS,SM,M)
   local S, len, MM, sMM, newSM,max,cands,lev,newcands, minOrbRepsS,c,orN,minoy,h,newSoN,newN,OI,y,m;

   if xS.generators=[] then
      return CopyStabChain(SM);
   fi;
   S:=CopyStabChain(xS);
   len:=Length(M);
   ChangeStabChain(S,M);
   newSM:=CopyStabChain(SM);
   if M<>[] then
      m:=Maximum(M);
   else
      m:=0;
   fi;
   max:=Maximum(StbcMaximumMovedPoint(S),m);
   cands:=[[SM,M,()]];
   for lev in [1..len] do
     newcands:=[];
     if S.generators=[] then
       cands:=Filtered(cands, x->x[2]{[lev..len]}=M{[lev..len]} and x[3]<>());
       cands:=List(cands, x->x[3]);
       if cands<>[] then
           if StbcIsTrivialStabChainNode(newSM) then
               if M<>[] then
                   StabChainForcePoint(newSM,M[1]);
               else
                   StabChainForcePoint(newSM,1);
               fi;
           fi;
           AddGeneratorsExtendSchreierTree(newSM,cands);
       fi;


       return newSM;
     fi;
     OI:=StbcEmptyOrbitInformation(S,max);
     for c in cands do
       if c[1].generators<>[] then
         orN:=StbcMinimalOrbitRepsCon(c[1],c[2]{[lev..len]},c[3]);
       else
         orN:=c[2]{[lev..len]};
       fi;
       for y in orN do
         if not OI[3][y] then
            ExtendOrbitInformation(OI,y);
         fi;
         minoy:=OI[4][y];
         if minoy<M[lev] then
             ChangeStabChain(S,[minoy]);
             h:=InverseRepresentative(S,y);
             return c[3]*h;
         fi;
         if minoy=M[lev] then
           if S.orbit[1]=M[lev] then
             h:=InverseRepresentative(S,y);
           else
             h:=();
           fi;
           newSoN:=CopyStabChain(c[1]);
           newSoN:=StbcStabilizer(newSoN,y/c[3]);
           newN:=OnSets(c[2],h);
           if newN{[lev+1..len]}<M{[lev+1..len]} then
             return c[3]*h;
           fi;
           Add(newcands,[newSoN,newN,c[3]*h]);
         fi;
       od;
     od;
     cands:=newcands;
     if S.orbit[1]=M[lev] then
       S:=S.stabilizer;
     fi;
   od;
   cands:=Filtered(cands, x->x[3]<>());
   cands:=List(cands, x->x[3]);
   if cands<>[] then
       AddGeneratorsExtendSchreierTree(newSM,cands);
   fi;

   return newSM;
end;





# G is a permutation group
# xGMM is a group that fixes MM as a partition and x as a set
# MM is a set of sets of the same cardinality
# x is a set of the same cardinality as the sets from MM, but not in MM
# the function tests whether MM+x is reducible
# if yes, then it returns a reducing permutation
# if no, then it returns the SetsSets-wise stabilizer of MM+x in G
SetsSetsReducibilityTestOneCard:=function(G,xGMM,MM,x)
    local   len,  sxMM,  cands,  lev,  newcands,  c,
            orNN,  orN,  y,  minreps,  minoy,  h,  newcandGroup,
            newN;




    if IsTrivial(G) then
        return G;
    fi;

    len:=Length(MM)+1;
    sxMM:=Union(MM,[x]);

    cands:=[[xGMM,sxMM,()]];
    for lev in [1..len] do
        newcands:=[];
        if IsTrivial(G) then
            cands:=Filtered(cands, x->x[2]{[lev..len]}=sxMM{[lev..len]} and x[3]<>());
            cands:=List(cands, x->x[3]);

            return ClosureGroup(xGMM,cands);
        fi;
        for c in cands do
            if not IsTrivial(c[1]) then
                orNN:=Filtered(c[2]{[lev..len]}, x->not IsPerm(IsCanonicalSetOrbitRep(Stbc(c[1]),Stbc(Stabilizer(c[1],x,OnSets)),x)));
            else
                orNN:=c[2]{[lev..len]};
            fi;
            for y in orNN do
                minreps:=SetCanonifiers(Stbc(G), Stbc(Stabilizer(G,y,OnSets)), y);

                minoy:=OnSets(y,minreps[1]);
                if minoy<sxMM[lev] then
                    return c[3]*minreps[1];
                fi;
                if minoy=sxMM[lev] then
                    h:=minreps[1];

                    newcandGroup:=c[1]^h;
                    newcandGroup:=Stabilizer(newcandGroup,minoy,OnSets);
                    newN:=OnSetsSets(c[2],h);
                    if newN{[lev+1..len]}<sxMM{[lev+1..len]} then
                        return c[3]*h;
                    fi;
                    Add(newcands,[newcandGroup,newN,c[3]*h]);

                fi;
            od;
        od;
        cands:=newcands;
        G:=Stabilizer(G, sxMM[lev], OnSets);
    od;

    cands:=Filtered(cands, x->x[3]<>());
    cands:=List(cands, x->x[3]);

    return ClosureGroup(xGMM,cands);
end;

SetsSetsCanonifiers:=function(G,GM,M)
    local   lens,  slices,  cands,  MM,  len,  cMM,  lev,  newcands,
            minSet,  cosReps,  c,   orNN,  y,  minreps,
            minoy,  h,  newcandGroup,  newN;

    if IsTrivial(G) then
        return [()];
    fi;

    lens:=Set(M,Length);
    slices:=List(lens, x->Filtered(M, y->Length(y)=x));
    cands:=[[GM,[],()]];

    for MM in slices do
        len:=Length(MM);

        cMM:=[];
        cands:=List(cands, c->[c[1],OnSetsSets(MM,c[3]),c[3]]);

        for lev in [1..len] do
            newcands:=[];
            if IsTrivial(G) then
                minSet:=cands[1][2];
                cosReps:=[];
                for c in cands do
                    if c[2]<minSet then
                        minSet:=c[2];
                        cosReps:=[c[3]];
                    elif c[2]=minSet then
                        AddSet(cosReps, c[3]);
                    fi;
                od;
                return cosReps;
            fi;
            for c in cands do
                if not IsTrivial(c[1]) then
                    orNN:=Filtered(c[2]{[lev..len]}, x->not IsPerm(IsCanonicalSetOrbitRep(Stbc(c[1]),Stbc(Stabilizer(c[1],x,OnSets)),x)));
                else
                    orNN:=c[2]{[lev..len]};
                fi;
                for y in orNN do
                    minreps:=SetCanonifiers(Stbc(G), Stbc(Stabilizer(G,y,OnSets)), y);

                    minoy:=OnSets(y,minreps[1]);
                    if not IsBound(cMM[lev]) then
                        cMM[lev]:=minoy;
                    fi;

                    if minoy<=cMM[lev] then
                        if minoy<cMM[lev] then
                            cMM[lev]:=minoy;
                        fi;


                        #     return c[3]*minreps[1];
                        # fi;
                        # if minoy=sxMM[lev] then
                        h:=minreps[1];

                        newcandGroup:=c[1]^h;
                        newcandGroup:=Stabilizer(newcandGroup,minoy,OnSets);
                        newN:=OnSetsSets(c[2],h);
                        #                    if newN{[lev+1..len]}<sxMM{[lev+1..len]} then
                        #                        return c[3]*h;
                        #                    fi;
                        Add(newcands,[newcandGroup,newN,c[3]*h]);
                    fi;
                od;
            od;
            cands:=Filtered(newcands, x->x[2][lev]=cMM[lev]);
            G:=Stabilizer(G, cMM[lev], OnSets);
        od;
    od;


    cosReps:=List(cands, x->x[3]);
    return cosReps;
end;
