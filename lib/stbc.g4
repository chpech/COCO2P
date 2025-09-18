
IsOverlappingStabChains:=function(S1,S2)
    local  nS1, nS2;
    
    nS1:=S1;
    nS2:=S2;
                 
    while true do 
        while true do
            if IsIdenticalObj(nS1,nS2) then
                Info(InfoCOCO,1, "S1 and S2 have a non-trivial overlap!");
                return true;
            fi;
            if not IsBound(nS2.stabilizer) then
                break;
            fi;
            nS2:=nS2.stabilizer;
        od;
        if not IsBound(nS1.stabilizer) then
            break;
        fi;
        nS1:=nS1.stabilizer;
    od;
    return false;
end;

            
IsReducedStabChain:=function(S)
    if IsBound(S.orbi) and (S.generators = [] or S.generators = [()]) then
        Info(InfoCOCO,1,"S is not reduced");
        Error("tst");
            
        return false;
    fi;
    if IsBound(S.stabilizer) then
        return IsReducedStabChain(S.stabilizer);
    fi;
    return true;
end;


IsConsistentStabChain:=function(S)
    local  g, h, stab;
    if not IsBound(S.orbit) then
        if S.generators <> [] then
            Info(InfoCOCO,1,"S has generators but no orbit!");
            return false;
        elif S.genlabels <> [] then
            Info(InfoCOCO,1,"S has no generators but genlabels!");
            return false;
        fi;
    else
        if not IsBound(S.stabilizer) then
            Info(InfoCOCO,1,"S has an orbit but no stabilizer!");
            return false;
        fi;
    
        
        g:=Group(S.generators,());
        h:=Stabilizer(g,S.orbit[1]);
        stab:=Group(S.stabilizer.generators,());
        if h <> stab then
            Info(InfoCOCO,1,"S.stabilizer is not the stabilizer of S.orbit[1] in S!");
            
            return false;
        fi;
    fi;
    
    if not IsBound(S.stabilizer) then
        return true;
    fi;
    
    return IsConsistentStabChain(S.stabilizer);
end;

Stbc:=StabChainMutable;

StbcCopy:=CopyStabChain;

StbcInsertTrivialStabilizer:=InsertTrivialStabilizer;

StbcIsTrivialStabChainNode:=function(S)
    return Length(S.generators)=0;
end;


StbcReduce:=ReduceStabChain;
StbcConjugate:=function(S,g)
   ConjugateStabChain(S,S,g,g);
end;


# still problematic
# StbcAugmentByNewGenerators:=function(S,lg)
#     local  M, sM,AppendStabChain,Augment,tS;
    
#     if lg <> [] then
#         StabChainStrong(S,lg,rec(base:=[]));
#     fi;
#     return;
    
#     # AppendStabChain:=function(S,sS)
#     #     local lS,lsS;
        
#     #     Assert(1, S.generators=[]);
        
#     #     lS:=S;
#     #     lsS:=sS;
        
#     #     while lsS.generators <> [] do
#     #         InsertTrivialStabilizer(lS, lsS.orbit[1]);
#     #         AddGeneratorsExtendSchreierTree(lS,lsS.generators);
#     #         lS:=lS.stabilizer;
#     #         lsS:=lsS.stabilizer;
#     #     od;
#     # end;
    
#     # Augment:=function(S,alg)
#     #     M:=Filtered(alg, g->g<>());
#     #     Assert(1,IsConsistentStabChain(S));
    
#     #     if M=[]  then
#     #         return;
#     #     fi;
        
#     #     if IsBound(S.orbit) then
#     #         AddGeneratorsExtendSchreierTree(S,M);
#     #         sM:=Filtered(M, g->S.orbit[1]^g = S.orbit[1]);
#     #         if sM <> [] then
#     #             if S.stabilizer.generators=[] then
#     #                 AppendStabChain(S.stabilizer,StabChain(Group(sM)));
#     #                 AddGeneratorsExtendSchreierTree(S,M);
#     #                 Assert(1,IsConsistentStabChain(S));
#     #             else
#     #                 Augment(S.stabilizer,sM);
#     #                 AddGeneratorsExtendSchreierTree(S,M);
#     #                 Assert(1,IsConsistentStabChain(S));
#     #             fi;
#     #         fi;
#     #     else
#     #         InsertTrivialStabilizer(S, SmallestMovedPointPerms(M));
#     #         AddGeneratorsExtendSchreierTree(S,M);
#     #     fi;
    
#     #     Assert(1,IsConsistentStabChain(S));
#     #     return;
#     # end;
    
#     # tS:=CopyStabChain(S);
    
#     # Augment(S, Set(lg, g->SiftedPermutation(S,g)));
#     # Assert(1,IsSubset(Group(S.generators,()),lg));
    
#     # return;
# end;


StbcAddGensExtOrb:=AddGeneratorsExtendSchreierTree;

    
StbcInvCosRep:=InverseRepresentative;

StbcSize:=SizeStabChain;

StbcMinimalOrbitReps:=function(S,dom)
    local orb, gens, repr, repidx, sch, im, i,j,k,ret,lengthes,max;

    if dom=[] then
      return [];
    fi;
    max:=Maximum(dom);
    max := Maximum(max,LargestMovedPointPerms(S.generators));

    
    sch:=BlistList([1..max],[]);
    repr:=[];
    gens:=S.generators;

    for i in dom do
        if not sch[i] then
            Add(repr, i);
            sch[i]:=true;
            orb:=[i];
            for j in orb do
                for k in [1..Length(gens)] do
                    im:= j ^ gens[k];
                    if not sch[im] then
                        sch[im]:=true;
                        Add(orb, im);
                    fi;
                od;
            od;
        fi;
    od;
    return repr;
end;



StbcOrbitsAndMap:=function(S,dom,max)
    local orb, gens, repr, repidx, sch, im, i,j,k,ret,lengthes,pt2oridx,orbs;

    if dom=[] then
      return [];
    fi;
    sch:=BlistList([1..max],[]);
    repr:=[];
    gens:=S.generators;
    pt2oridx:=[];
    orbs:=[];
    for i in dom do
        if not sch[i] then
            Add(repr, i);
            sch[i]:=true;
            orb:=[i];
            pt2oridx[Position(dom,i)]:=Length(repr);
            for j in orb do
                for k in [1..Length(gens)] do
                    im:= j ^ gens[k];
                    if not sch[im] then
                        sch[im]:=true;
                        Add(orb, im);
                        pt2oridx[Position(dom,im)]:=Length(repr);
                    fi;
                od;
            od;
            Add(orbs,orb);
        fi;
    od;
    return rec(orbits:=orbs, map:=pt2oridx);
end;


StbcRefineOrbits:=function(S,part,max)
   local orbs,n,respart,orb,np,i;
   orbs:=part.orbits;

   n:=0;
   respart:=rec(orbits:=[], map:=[]);
   for orb in orbs do
      np:=  StbcOrbitsAndMap(S,orb,max);
      for i in [1..Length(np.map)] do
         respart.map[orb[i]]:=np.map[i]+n;
      od;
      Append(respart.orbits,np.orbits);
#      Append(respart.map, np.map+n);
      n:=n+Length(np.orbits);
   od;
   return respart;
end;



# returns minimal orbit representatives of S^g on dom
StbcMinimalOrbitRepsCon:=function(S,dom,g)
    local orb, gens, repr, repidx, sch, im, i,j,k,ret,lengthes;

    if dom=[] then
      return [];
    fi;


    sch:=BlistList([1..Maximum(dom)],[]);
    repr:=[];
    gens:=S.generators;

    for i in dom do
        if not sch[i] then
            Add(repr, i);
            sch[i]:=true;
            orb:=[i];
            for j in orb do
                for k in [1..Length(gens)] do
                    im:= ((j/g)^gens[k])^g;
                    if not sch[im] then
                        sch[im]:=true;
                        Add(orb, im);
                    fi;
                od;
            od;
        fi;
    od;
    return repr;
end;

StbcMaximumMovedPoint:=function(S)
  return LargestMovedPointPerms(S.generators);
end;

StbcMinimalOrbitRep:=function ( G, d )
    local  orb, max, new, gen, pnt, img,min;

    max := 0;
    for gen  in G.generators  do
        if max < LargestMovedPointPerm( gen )  then
            max := LargestMovedPointPerm( gen );
        fi;
    od;
    if not d in [ 1 .. max ]  then
        return  d ;
    fi;
    min:=d;
    orb := [ d ];
    new := BlistList( [ 1 .. max ], [ 1 .. max ] );
    new[d] := false;
    for pnt  in orb  do
        for gen  in G.generators  do
            img := pnt ^ gen;
            if new[img]  then
                if img<min then
                   min:=img;
                fi;
                Add( orb, img );
                new[img] := false;
            fi;
        od;
    od;

    return min;
end;

StbcChange:=ChangeStabChain;

StbcStabilizer:=function(S,x)
    StbcChange(S,[x]);
    if IsBound(S.orbit) and S.orbit[1]=x then
        return S.stabilizer;
    else
        return S;
    fi;
end;



StbcOrbits:=function(S, D)
    return OrbitsPerms(S.generators,D);
end;

StbcOrbit:=function(S, pt)
    return OrbitStabChain(S,pt);
end;

StbcForce:=StabChainForcePoint;

StbcReduce:=ReduceStabChain;


StbcGroup:=GroupStabChain;



# Orbit Informations: [gens,repr,sch,pt2orbrep,schreierforrest]
# gens: generators
# repr: list of minimal representatives of already computed orbits
# sch:  Blist such that sch[i]=true if i is in one of the already computed orbits
# pt2orbrep: a list that pt2orbres[i]=j if j is in repr and i is in the orbit generated by j
# schreierforest: a list representing the Schreier-Forest with roots equal to the minimal orbit reps

StbcEmptyOrbitInformation:=function(S,max)
   return [ShallowCopy(S.generators), [], BlistList([1..max],[]),[],[]];
end;

ExtendOrbitInformation:=function(OI, i)
  local orb,min,j,k,im;

  if OI[3][i] then
     return;
  fi;

  orb:=[i];
  min:=i;
  OI[3][i]:=true;
  OI[5][i]:=-Length(OI[2])-1;
  for j in orb do
    for k in [1..Length(OI[1])] do
          im:= j ^ OI[1][k];
          if not OI[3][im] then
              OI[3][im]:=true;
              Add(orb, im);
              OI[5][im]:=k;
              if im<min then
                 min:=im;
              fi;
          fi;
      od;
  od;
  for j in orb do
    OI[4][j]:=min;
  od;
  Add(OI[2],min);
  return;
end;


StbcInverseRepresentativeInOrbitInformation:=function(OI,c)
   local i,h,k,m,g;
   ExtendOrbitInformation(OI,c);
   i:=c;h:=();m:=OI[2][c];
   while OI[5][i]>0 do
      k:=OI[1][OI[5][i]];
      h:=h/k;
      i:=i/k;
   od;
   i:=m;g:=();
   while OI[5][i]>0 do
      k:=OI[1][OI[5][i]];
      g:=g/k;
      i:=i/k;
   od;
   if c^(h/g)<>m then
      Error("hmmm...");
   fi;
   return h/g;
end;

StbcExtend:=function(S,l,i)
  if l=[] then
     return;
  fi;
  StabChainForcePoint(S,i);
  AddGeneratorsExtendSchreierTree(S,l);
end;


StbcIntersection:=function(S1,S2)
   return StabChainMutable(Intersection(StbcGroup(S1),StbcGroup(S2)));
end;
