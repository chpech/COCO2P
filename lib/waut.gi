#############################################################################
##
##  waut.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of the functions filtering AAut for CAut
##
#############################################################################


#
# This file contains functions for the computation of the color automorphism
# group of a coherent configuration.



InstallGlobalFunction(CheckElm,
function(p,xcgr1,xcgr2)
    local m1,m2,g1,g2,h,o1,o2;

    g1:=xcgr1.T;
    g2:=xcgr2.T;

    m1:=List([1..Rank(g1)], x->x^p);
    m2:=[1..Rank(g1)];

    o1:=BuildXCgrObject(g1,m1);
    o2:=BuildXCgrObject(g2,m2);
    h:=IsomorphismPbagObjects(o1, o2, XCgrInvariant);

    return h;
end);

InfoW1:=Ignore;

InstallGlobalFunction(FindCosRep,
function(H, resH, xcgr1, xcgr2, h, res)
    local x,m1,m2,o1,o2,y,nh,pt,i,crep;

    InfoW1("Entering FindCosRep.\n");
    if StbcIsTrivialStabChainNode(H) then

        x:=CheckElm(h,xcgr1,xcgr2);
        if x <> false then
            Add(res, x);
            return h;
        fi;
        return false;
    fi;

    m1:=H.part.map;
    m2:=Permuted(m1,h);
    InfoW1(h,"\n",m1,"\n",m2,"\n");

    ChangeColoringOfXCgr(xcgr1,m1);
    ChangeColoringOfXCgr(xcgr2,m2);
    o1:=BuildXCgrObject(xcgr1);
    o2:=BuildXCgrObject(xcgr2);
    y:=IsomorphismPbagObjects(o1,o2,XCgrInvariant);
    if y=false then
        InfoW1("/\c");
       return false;
    fi;

    pt:=H.orbit[1];

    for i in H.orbit do
        # check if i is the first element of its orbit in reH.stabilizer
        if resH.stabilizer.part.orbits[resH.stabilizer.part.map[i]][1]<>i then
            COCOPrint("%\c");
            continue;
        fi;
        crep:=StbcInvCosRep(H, i)^-1;
        nh:=crep*h;
        x:=FindCosRep(H.stabilizer, resH.stabilizer, xcgr1,xcgr2,nh,res);
        if x <> false then
            return x;
        fi;
    od;
    return false;
end);

InstallGlobalFunction(CheckGroup,
function(xcgr1, xcgr2, S, part, result)
   local newpart,m, o1,o2,y,pt,resH, i, xi, crep;

   if StbcIsTrivialStabChainNode(S) then
       resH:=EmptyStabChain([],());
       resH.part:=rec(map:=[1..Length(part.map)],
                      orbits:=List([1..Length(part.map)], x->[x]));
       return resH;
   fi;

   newpart:=StbcRefineOrbits(S,part, RankOfColorGraph(xcgr1.T));
   S.part:=newpart;

   pt:=S.orbit[1];
   resH:=EmptyStabChain([], (), pt);
   resH.stabilizer:=CheckGroup(xcgr1,xcgr2,S.stabilizer, newpart,result);

   Append(resH.generators,resH.stabilizer.generators);

   for xi in [2..Length(S.orbit)] do
       i:=S.orbit[xi];
       if IsBound(resH.transversal[i]) then
           continue;
       fi;
       if resH.stabilizer.part.orbits[resH.stabilizer.part.map[i]][1]<>i then
           COCOPrint("#\c");
           continue;
       fi;
       crep:=StbcInvCosRep(S, i)^-1;
       y:=FindCosRep(S.stabilizer, resH.stabilizer, xcgr1, xcgr2, crep, result);

       if y <> false then
           COCOPrint(".\c");
           StbcAddGensExtOrb(resH, [y]);
       fi;
   od;
   resH.part:=StbcRefineOrbits(resH, S.part,RankOfColorGraph(xcgr1.T));
   return resH;
end);
