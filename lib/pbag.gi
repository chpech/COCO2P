#############################################################################
##
##  pbag.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of the Coco partition backtracker
##
#############################################################################


# ported from $pbag.g,v 1.3 1999/08/25 19:38:24 pech Exp $
# PBAG (Partition Backtracking Algorithm using GAP)

# In the following functions for the computation with the symmetries
# of combinatorial objects are provided. In particular:

# FindBaseObject
# AutGroupOfPbagObject
# IsomorphismPbagObjects

# In the future also a function CanonicalLabelingObject will be
# included (at least this is planned and should not be too difficult)

# A combinatorial object is a construct from a finite point-set Omega (the
# existence of points is crucial in this approach). By "construct" is
# meant a member of the usual Bourbaki-ladder (I will not explain it here in
# detail but essetially it means that any finite object that
# is built up from points is allowed such as graphs, designs, codes, ...)

# Our combinatorial objects will allways have colored points.

# The set of points will be assumed to be the set [1..v]

# The set of colors of points also has to be a set of the form [1..c]

# Representation of combinatorial objects:
# A combinatorial Object is a record with the following components
# rec(
#     T:=??,
#     nc:=??,
#     v:=??
#     ncp:=?
#     fvc:=??,
#     fcv:=??,
#     S:=??
#     ST:=
#     );
# T referes to some data structure describing the object. This field
# is special because the program will never access it
# directly. Moreover it can have any name (I only chose T for brevity).
# Later I will described why this is so.

# nc is a number that describes a global invariant of the object
# (e.g. the number of edge-colors in a CGR). It is included here for convenience
# in general it is not needed in the algorithm. If no good global
# invariant is known then one can just put nc:=1;

# v is the number of points of T

# ncp  contains the
# number of color classes on points (NumberofColorclassesonPoints).

# fvc is a function that maps each point to its color. It is
# implemented as a list where at the index v the color of v is stored

# fcv is the inverse function of fvc. To each color c the set of points
# is mapped which have color c

# S,ST are internal fields for the algorithm. The partial bases are
# stored in there. They should allways be initialized with the empty
# list [].

# during the algorithm successively the point set gets partitioned
# using a local invariant of the points of the object. This local
# invariant has to  be provided by the user. It gets a combinatorial
# object  and a point and has to compute something that preserves the
# symmetries of the object. The second function the user has to supply
# is a good hashing function for invariants. It takes an invariant
# and returns a number from [1.._hashsize]. such that (ideally)
# different invariants get different numbers (collisions are detected
# and resolved autommatically). Finally the last function the user has to
# provide is a test, if a given permutation is an Isomorphism from one object
# to another (two objects of the certain type and a permutation on points are
# the input and the return values may be true or false)

# A few invariants are allready provided: namely for complete colored
# multigraphs and for complete colored ternary relations.

# Note that the speed of the algorithm dramatically depends on the
# quality of the invariant. If the invariant does not distinguish the
# points enough then the algorithm will perform more or less the
# exhaustive brute force search. If on the other hand the invariant is
# very good but very expensive to compute, the speed of the
# algorithm may  suffer too.

# A last note about the implementation. This preliminary version is
# not yet optimized for speed (it does e.g. some very foolish things
# when changing the base during the computation of the automorphism
# group of  an object). This may influence the usefulness of the
# program in that it is only feasible for rathe small v.  However, no
# speed-tests were done up to now (for CGRs graphs up to 200 vertices were
# handeled very well; this means in a few seconds)

# This program was inspired from some sources as e.g. I.Faradzev
# (the algorithm for the aut function in COCO), J.S.Leon (his
# paper "Computing Automorphism Groups of Combinatorial Objects" was
# very helpful in understanding some very essential rejection rules
# during back-tracking in AutGroupOfPbagObject) and G.Tinhofer (with his
# description of an isomorphism test for CGRs using total degree partitions
# the whole project was initiated), M.Klin who needed a program for
# the computation of  Isomorphisms of colored graphs in his normalizer
# algorithm for 2-closed groups and who needed the implementation to
# be ready within "a few days".


# The first version of this program was writted by:
#           Ch. Pech, March 15, 1997 in Beer-Sheva, Israel
#           e-mail(Israel): pech@cs.bgu.ac.il
#           e-mail(home):   pech@virgo.sax.de

# The following changes were done by Ch.P. on November 12, 2007 in Beer-Sheva, Israel
#           e-mail(home): cpech@freenet.de
#           e-mail(Israel): pech@cs.bgu.ac.il

# the structure of combinatorial objects is now equiped with  the
# stabilizer chain of a sub-group of its automorphism group.
# This information is used in order to speed up  the
# point-stabilization. It is used, too, when computing the
# automorphism group of an object or when testing for
# isomorphism.

# The following changes were done by Ch.P. in November 2008 in Futog, Serbia
#           e-mail(home): cpech@freenet.de
#
# The Hashing is now done using the facilities provided by GAP4.
#
# The following changes were done by Ch.P. in November 2012 in Futog, Serbia
#           e-mail(home): cpech@freenet.de
#
# The hashtable code changed in GAP 4.5.
# the old hashtable code from GAP 4.5 was canibalized and put into the
#           COCO2p-namespace
#

# At the end of the file a new type for partitions is implemented. It should make
# splitting classes cheaper.
# This would make necessary a change in the structure of combinatorial objects:
# rec(
#     T:=??,
#     nc:=??,
#     v:=??,
#     part:=??,
#     S:=??
#     ST:=
#     );
# part contains the partition in the partition formar described elsewhere
# the field ncp was replaced by a function NCP(part)
# the field fvc was replaced by a function FVC(part,v)
# the field pcv was replaced by a function FCV(part,c)
#   this function is rather exensive. Use it rarely!
# Note that this type for partitions is not yet integrated into PBAG
# I am not yet convinced that this implementation will really be
# faster than the existing one.



# Now a few internal constants:

InstallValue(pbagGlobalData, rec( useCache := true,
                                     cache := [],
                                  cacheHit := 0,
                                 cacheMiss := 0));

SetInfoLevel(InfoPbag,0);

InstallGlobalFunction(ShallowCopyPbagObject,
function(object)
    local rf,newobj,i;

    rf:=RecFields(object);
    newobj:=ShallowCopy(object);
    newobj.fvc:=ShallowCopy(object.fvc);
    newobj.fcv:=List(newobj.fcv, ShallowCopy);
    newobj.S:=ShallowCopy(newobj.S);
    newobj.ST:=ShallowCopy(newobj.ST);
    newobj.stabChain:=CopyStabChain(newobj.stabChain);
    return newobj;
end);

InstallGlobalFunction(PbagSemiStep,
function(object,c, invariant)
    local cls, partition,j,inv,pos,f,
          ptarray, orbscls,i,hashtbl,fixed,newcolor;

    Info(InfoPbag,2,"PbagSemiStep: enter.");

    hashtbl:=SparseHashTable@(invariant.hashinv);
    ptarray:=[];

    cls:=object.fcv[c];

    orbscls:=Set(StbcOrbits(object.stabChain,cls),Set);
    for i in [1..Length(orbscls)] do
        inv:=invariant.finv(object, orbscls[i][1]);
        newcolor:=AddHashEntry@(hashtbl,inv,Length(ptarray)+1);
        if newcolor<>fail then
           Add(ptarray,[]);
        else
           newcolor:=GetHashEntryAtLastIndex@(hashtbl);
        fi;
        UniteSet(ptarray[newcolor],Set(orbscls[i], x->PositionSet(cls,x)));
    od;

    return [hashtbl,ptarray];
end);

InstallGlobalFunction(PbagSemiStepWithGivenHashTable,
function(object,c,invariant,hashtbl)
    local cls, partition,j,inv,pos,
          ptarray, orbscls,i,fixed,newcolor;

    Info(InfoPbag,2, "PbagSemiStepWGHT: enter.");

    ptarray:=List([1..HashTableSize@(hashtbl)], x->[]);

    cls:=object.fcv[c];

    orbscls:=Set(StbcOrbits(object.stabChain,cls),Set);
    for i in [1..Length(orbscls)] do
        inv:=invariant.finv(object, orbscls[i][1]);
        newcolor:=GetHashEntry@(hashtbl, inv);
        if newcolor=fail then
              Info(InfoPbag,2, "PbagSemiStepWGHT: fail.");
              return fail;
        fi;
        UniteSet(ptarray[newcolor],Set(orbscls[i], x->PositionSet(cls,x)));
    od;

    return [hashtbl,ptarray];
end);



InstallGlobalFunction(RecolorPbagObject,
function(object, color, partition)
    local oldclass,ct,l,i;


    oldclass:=object.fcv[color];
    ct:=[color]; Append(ct, [object.ncp+1..object.ncp+Length(partition)-1]);

    for i in [1..Length(ct)] do
        object.fcv[ct[i]]:=oldclass{partition[i]};
        l:=Length(object.fcv[ct[i]]);
        object.fvc{object.fcv[ct[i]]}:=ListWithIdenticalEntries(l,0)+ct[i];
        if l=1 then
            Add(object.ST, object.fcv[ct[i]][1]);
        fi;
    od;

    object.ncp:=object.ncp+Length(partition)-1;
end);

InstallGlobalFunction(RecolorPointOfPbagObject,
function(object, point)
    local color,class,index,partition,p1,p2;

    color:=object.fvc[point];
    class:=object.fcv[color];
    index:=Position(class, point);
    p1:=[1..index-1];
    p2:=[];
    if index<Length(class) then
        p2:=[index+1..Length(class)];
    fi;
    partition:=[Concatenation(p1,p2), [index]];
    RecolorPbagObject(object, color, partition);
    Add(object.S,point);
    object.stabChain:=CopyStabChain(StbcStabilizer(object.stabChain,point));
end);

InstallGlobalFunction(PbagStabilStep,
function(object, TInv,level,inst)
    local i,part, invp;

    i:=1;

    Info(InfoPbag,2, "PbagStabilStep: enter.");
    while i <=object.ncp do
        if Length(object.fcv[i])<>1 then
            if pbagGlobalData.useCache then
                if not IsBound(pbagGlobalData.cache[level]) then
                    pbagGlobalData.cache[level]:=[];
                fi;

                if not IsBound(pbagGlobalData.cache[level][i]) then
                    pbagGlobalData.cache[level][i]:=[];
                fi;

                if not IsBound(pbagGlobalData.cache[level][i][inst]) then
                    pbagGlobalData.cacheMiss:=pbagGlobalData.cacheMiss+1;
                    part:=PbagSemiStep(object,i,TInv);
                    pbagGlobalData.cache[level][i][inst]:=part;
                else
                    pbagGlobalData.cacheHit:=pbagGlobalData.cacheHit+1;
                    part:=pbagGlobalData.cache[level][i][inst];
                fi;
            else
                part:=PbagSemiStep(object,i,TInv);
            fi;
            part:=part[2];
            if Length(part)> 1 then
                RecolorPbagObject(object, i, part);
            fi;
        fi;
        i:=i+1;
    od;
end);

InstallGlobalFunction(PbagSimultaneousStabilStep,
function(t1,t2,TInv,level, instance)
    local i,
          part1,part2,
          p1,p2,
          l1,   l2;

    i:=1;

    Info(InfoPbag,2,"PbagSimultaneousStabilStep: enter.");
    while i <= t1.ncp do
        if Length(t1.fcv[i])<>1 then


            if pbagGlobalData.useCache then
                if not IsBound(pbagGlobalData.cache[level]) then
                    pbagGlobalData.cache[level]:=[];
                fi;

                if not IsBound(pbagGlobalData.cache[level][i]) then
                    pbagGlobalData.cache[level][i]:=[];
                fi;

                if not IsBound(pbagGlobalData.cache[level][i][instance]) then
                    part1:=PbagSemiStep(t1,i,TInv);
                    pbagGlobalData.cacheMiss:=pbagGlobalData.cacheMiss+1;
                    pbagGlobalData.cache[level][i][instance]:=part1;
                else
                    part1:=pbagGlobalData.cache[level][i][instance];
                    pbagGlobalData.cacheHit:=pbagGlobalData.cacheHit+1;
                fi;
            else
                part1:=PbagSemiStep(t1,i,TInv);
            fi;

            part2:=PbagSemiStepWithGivenHashTable(t2,i,TInv,part1[1]);
            if part2=fail then
               return false;
            fi;

            p1:=part1[2];
            p2:=part2[2];
            l1:=List(p1, x->Length(x));
            l2:=List(p2, x->Length(x));
            if l1<>l2 then
                return false;
            fi;
            if Length(p1)>1 then
                RecolorPbagObject(t1, i, p1);
                RecolorPbagObject(t2, i, p2);
            fi;
        fi;
        i:=i+1;
    od;
    return true;
end);

InstallGlobalFunction(PbagStabil,
function(object, TInv,level)
    local ncp,nncp,inst;

    Info(InfoPbag,2, "PbagStabil: enter.");
    ncp:=object.ncp;
    PbagStabilStep(object, TInv,level,1);
    nncp:=object.ncp;
    inst:=2;

    while nncp> ncp do
        Info(InfoPbag,2, "Step.");
        PbagStabilStep(object, TInv,level,inst);
        inst:=inst+1;
        ncp:=nncp;
        nncp:=object.ncp;
    od;
end);

InstallGlobalFunction(PbagSimultaneousStabil,
function(t1, t2, TInv,level)
    local ncp, nncp,inst;

    Info(InfoPbag, 2, "PbagSimultaneousStabil: enter.");
    if t1.ncp<>t2.ncp then
        return false;
    fi;

    ncp:=t1.ncp;

    if PbagSimultaneousStabilStep(t1,t2, TInv,level,1)=false then
        return false;
    fi;

    nncp:=t1.ncp;
    inst:=2;
    while nncp>ncp do
        Info(InfoPbag,2,"Step.");

        if PbagSimultaneousStabilStep(t1,t2,TInv,level,inst)=false then
            return false;
        fi;
        inst:=inst+1;
        ncp:=nncp;
        nncp:=t1.ncp;
    od;
    return true;
end);

InstallGlobalFunction(PbagGetMaxColorClass,
function(object)
    local lengthes,i,max;

    lengthes:=List(object.fcv, x->Length(x));
    max:=[0, 0];
    for i in [1..Length(lengthes)] do
        if lengthes[i]>max[1] then
            max[1]:=lengthes[i];
            max[2]:=i;
        fi;
    od;
    if max[1]=1 then
        return false;
    fi;

    return max[2];
end);

InstallGlobalFunction(PbagGetMinColorClass,
function(object)
    local lengthes,i,min;

    lengthes:=List(object.fcv, x->Length(x));
    min:=["infinity", 0];
    for i in [1..Length(lengthes)] do
        if lengthes[i]<min[1] and lengthes[i]<>1 then
            min[1]:=lengthes[i];
            min[2]:=i;
        fi;
    od;

    return min[2];
end);

InstallGlobalFunction(PbagGetNewColorClass,
function(object)
   local lengthes,rl,cl,length;

    lengthes:=List([1..Length(object.fcv)], x->[x,Length(object.fcv[x])]);
    rl:=Filtered(List(lengthes, x->x[2]), x->x>1);
    cl:=Collected(rl);
    Sort(cl, function(x,y) return x[2]<y[2];end);
    cl:=Filtered(cl, x->x[2]=cl[1][2]);
    cl:=List(cl, x->x[1]);
    length:=Minimum(cl);
    return First(lengthes, x->x[2]=length)[1];
end);

InstallGlobalFunction(PbagFindBase,
function(object,TInv)
    local color,point;

    if Length(object.ST)=object.v then
        return object.S;
    fi;

    color:=PbagGetMaxColorClass(object);
    point:=object.fcv[color][1];

    RecolorPointOfPbagObject(object, point);
    PbagStabil(object, TInv,1);
    return PbagFindBase(object,TInv);
end);

InstallGlobalFunction(PbagFindCosetRep,
function(t1,t2, TInv, level)
    local g,p1,p2,flag, color, point, class, i, nt1,nt2,NH,orb;

    Info(InfoPbag,2,"PbagFindCosetRep: enter.");
    if not PbagSimultaneousStabil(t1, t2, TInv, level) then
        return false;
    fi;

    if Length(t1.ST)=t1.v then
        p1:=PermList(t1.fvc);
        p2:=PermList(t2.fvc);
        g:=p1*p2^-1;
        if not TInv.autTest(t1,g) then
            return false;
        fi;
        Info(InfoPbag,1,"found!, ", level, "\t",g,".");
        return g;
    fi;

    color:=PbagGetMaxColorClass(t1);
    point:=t1.fcv[color][1];

    class:=ShallowCopy(t2.fcv[color]);

    while class<>[] do
        Info(InfoPbag,2,"next\t", Length(class), ".");

        i:=class[1];
        nt1:=ShallowCopyPbagObject(t1);
        nt2:=ShallowCopyPbagObject(t2);
        RecolorPointOfPbagObject(nt1, point);
        RecolorPointOfPbagObject(nt2, i);
        Info(InfoPbag,2, "TFindCoset: trying to map ", point," to ",i,".");
        g:=PbagFindCosetRep(nt1, nt2, TInv,level+1);
        if g<> false then
            return g;
        fi;

        orb:=StbcOrbit(t2.stabChain, i);
        SubtractSet(class, orb);
    od;


    return false;
end);

InstallGlobalFunction(PbagCopyStabChainNode,
function(S,T)
    local rf,newobj,i;


    rf:=RecFields(T);
    for i in rf do
        S.(i):=T.(i);
    od;
end);

InstallGlobalFunction(PbagExtendStabChain,
function(S,T,i)
   local node;
   if not IsBound(S.orbit) then
       PbagCopyStabChainNode(S,T);
   else
     StbcChange(S,[i]);
     if S.orbit[1]<>i then
       PbagCopyStabChainNode(S,T);
     else
       S.stabilizer:=T;
       StbcExtend(S,T.generators,i);
     fi;
   fi;
end);

InstallGlobalFunction(PbagFindAutGroup,
function(object, TInv,level)
    local color, point,nobject, nnobject,nimgobject,
          g, NH, NNH,class,orbPnt,i, done,ng;

    Info(InfoPbag,2,"PbagFindAutGroup: enter at level ", level, ".");

    if Length(object.ST)=object.v then
        Info(InfoPbag,1,"PbagFindAutGroup: Base = ", object.S,"\n");
        return;
    fi;

    done:=[];
    color:=PbagGetMaxColorClass(object);
    class:=Set(object.fcv[color]);
    point:=class[1];

    nobject:=ShallowCopyPbagObject(object);

    RecolorPointOfPbagObject(nobject, point);
    PbagStabil(nobject, TInv,level+1);

    PbagFindAutGroup(nobject, TInv, level+1);
    Add(done,point);


    PbagExtendStabChain(object.stabChain,nobject.stabChain,point);
    orbPnt:=Set(Concatenation(StbcOrbits(object.stabChain, done)));
    SubtractSet(class, orbPnt);

    Info(InfoPbag,3,Set(object.fcv[color]), "\t", color, "\t", object.fvc[point], ".");
    while class<>[] do
        Info(InfoPbag,2,"next coset\t", Length(class), ".");
        i:=class[1];
        Add(done, i);
        nnobject:=ShallowCopyPbagObject(object);
        nimgobject:=ShallowCopyPbagObject(object);
        RecolorPointOfPbagObject(nnobject, point);
        RecolorPointOfPbagObject(nimgobject, i);
        Info(InfoPbag,2,"Trying to map ", point, " to ", i,".");
        g:=PbagFindCosetRep(nnobject, nimgobject, TInv, level+1);
        if g <> false then
            Info(InfoPbag,2,g, ".");
            StbcExtend(object.stabChain,[g],point);
        fi;

        orbPnt:=Set(Concatenation(StbcOrbits(object.stabChain, done)));
        SubtractSet(class, orbPnt);
    od;

    return;
end);

InstallGlobalFunction(PbagFindIsomorphism,
function(object, imgobject, TInv, level)
    local color, point,nobject, nimgobject,
          newgroup, p1,p2,g,ok,class,orbs,i,flag,
          reps,snew,niG;

    Info(InfoPbag,1,"PbagFindIsomorphism: enter at level ", level, ".");

    flag:=PbagSimultaneousStabil(object, imgobject, TInv, level);
    if not flag then
        return false;
    fi;


    if Length(object.ST)=object.v then
        p1:=PermList(object.fvc);
        p2:=PermList(imgobject.fvc);
        g:=p1*p2^-1;
        if not TInv.test(object,imgobject,g) then
            return false;
        fi;
        return g;
    fi;

    color:=PbagGetNewColorClass(object);
    point:=object.fcv[color][1];

    class:=Set(ShallowCopy(imgobject.fcv[color]));

    while class<>[] do
        Info(InfoPbag,1,"Iso: ", Length(class), "\t", Length(object.fcv[color]), ".");
        i:=class[1];
        nobject:=ShallowCopyPbagObject(object);
        nimgobject:=ShallowCopyPbagObject(imgobject);
        RecolorPointOfPbagObject(nobject, point);
        RecolorPointOfPbagObject(nimgobject, i);
        g:=PbagFindIsomorphism(nobject, nimgobject, TInv,level+1);
        if g<>false then
            return g;
        fi;
        SubtractSet(class,StbcOrbit(imgobject.stabChain,i));
    od;

    return false;
end);

InstallGlobalFunction(PbagFindIsomorphismInGroup,
function(GG,SU,h,object, imgobject, TInv, level)
    local color, point,nobject, nimgobject,
          newgroup, p1,p2,g,ok,class,orbs,i,flag,
          reps,snew,niS,newSU,gorb,newh,olst,nlst;

    Info(InfoPbag,1,"PbagFindIsomorphismInGroup: enter at level ", level, ".");


    olst:=Length(object.ST);
    flag:=PbagSimultaneousStabil(object, imgobject, TInv, level);
    if not flag then
        return false;
    fi;
    nlst:=Length(object.ST);

    if Length(object.ST)=object.v then
        p1:=PermList(object.fvc);
        p2:=PermList(imgobject.fvc);
        g:=p1*p2^-1;
        if not g in GG then
           Info(InfoPbag,1,g,".");
           return false;
        fi;
        if not TInv.test(object,imgobject,g) then
           return false;
        fi;
        return g;
    fi;

    for i in [olst+1..nlst] do
       point:=object.ST[i];
       gorb:=point^h;
       StbcForce(SU,gorb);
       if not imgobject.ST[i] in SU.orbit then
          return false;
       fi;
       StbcForce(SU,imgobject.ST[i]);
       h:=h*(StbcInvCosRep(SU,point^h));
       SU:=SU.stabilizer;
    od;

    color:=PbagGetNewColorClass(object);
    point:=object.fcv[color][1];
    gorb:=point^h;
    StbcForce(SU,gorb);
    gorb:=Set(StbcOrbit(SU,gorb));
    class:=Set(ShallowCopy(imgobject.fcv[color]));
    class:=Intersection(class, gorb);

    while class<>[] do
        Info(InfoPbag,1,"Iso: ", Length(class), "\t", Length(object.fcv[color]), ".");
        i:=class[1];
        nobject:=ShallowCopyPbagObject(object);
        nimgobject:=ShallowCopyPbagObject(imgobject);
        RecolorPointOfPbagObject(nobject, point);
        RecolorPointOfPbagObject(nimgobject, i);
        StbcForce(SU,i);
        newSU:=StbcStabilizer(SU,i);
        newh:=h*StbcInvCosRep(SU,point^h);
        g:=PbagFindIsomorphismInGroup(GG,newSU,newh,nobject, nimgobject, TInv,level+1);
        if g<>false then
            return g;
        fi;
        SubtractSet(class,StbcOrbit(imgobject.stabChain,i));
    od;

    return false;
end);


InstallGlobalFunction(PbagInitialize,
function()
    pbagGlobalData.cache:=[];
end);

InstallGlobalFunction(AutGroupOfPbagObject,
function(object, H, TInv)
    local t,s,h;
    PbagInitialize();
    t:=ShallowCopyPbagObject(object);
    PbagFindAutGroup(t,TInv,1);
    ReduceStabChain(t.stabChain);
    return Group(ShallowCopy(t.stabChain.generators),());
end);

InstallGlobalFunction(IsomorphismPbagObjects,
function(t1, t2, TInv)
    local tt1,tt2;

    if (t1.v<>t2.v) then
        return false;
    fi;

    PbagInitialize();

    tt1:=ShallowCopyPbagObject(t1);
    tt2:=ShallowCopyPbagObject(t2);

    return PbagFindIsomorphism(tt1,tt2,TInv,1);
end);

InstallGlobalFunction(IsomorphismPbagObjectsInGroup,
function(t1, t2, G, TInv)
    local tt1,tt2,iS,SG;

    if (t1.v<>t2.v) then
        return false;
    fi;

    PbagInitialize();

    tt1:=ShallowCopyPbagObject(t1);
    tt2:=ShallowCopyPbagObject(t2);
    SG:=StbcReduce(StabChain(G));
    iS:=StbcIntersection(tt2.stabChain,StabChain(G));
    return PbagFindIsomorphismInGroup(G,CopyStabChain(SG),(),iS,tt1,tt2,TInv,1);
end);


################################################################################
# Partition Datatype:                                                          #
################################################################################
# A partition is a data-structure with 6 components:
# [firsts,lasts,lengths,next,prev,fvc]
#  - the classes are numbered consecutively by the integers 1..x
#  - classes are modelled by doubly linked lists of vertices
#  firsts is a list that has in position "i" the first vertex of class "i"
#  lasts is a list that has in position "i" the last vertex of class "i"
#  lengths is a list that has in position "i" the length of class "i"
#  next is a list that has in position "v" the next vertex after "v" of the same color
#     if such a vertex does not exist, then next[v]=0
#  prev is a list that has in position "v" the previous vertex of the same color as "v"
#     if such a vertex does not exist, then prev[v]=0
#  fvc is a list that has in position "v" the number of the class of which "v" is an element
#
# The structure of partitions is designed such that refining a partition is relatively cheap.
# So far joining of partition classes is not supported, as this is not necessary in the partition
# backtracking algorithm PBAG
## PBAGTrivialPartition:=function(n)
##    local firsts,lasts,lengths,next,prev,fvc;
##
##    firsts:=[1];
##    lasts:=[n];
##    lengths:=[n];
##    next:=[2..n]; Add(next,0);
##    prev:=[0..n-1];
##    fvc:=List([1..n], x->1);
##    return [firsts,lasts,lengths,next,prev,fvc];
## end;
##
## PBAGCopyPartition:=function(part)
##    return List(part, ShallowCopy);
## end;
##
## firsts:=1;
## lasts:=2;
## lengths:=3;
## next:=4;
## prev:=5;
## fvc:=6;
##
## NCP:=function(part)
##    return Length(part[firsts]);
## end;
##
## FVC:=function(part,v)
##    return part[fvc][v];
## end;
##
## FCV:=function(part,c)
##    local class,v;
##
##    class:=[];
##    v:=part[firsts][c];
##    while v<>0 do
##       Add(class,v);
##       v:=part[next][v];
##    od;
##    return class;
## end;
##
## # this function recolors a vertex v to color c
## # c must be larger than fvc[v]
## # v must not be the first vertex in its color class
## PBAGRecolorVertexOfPartition:=function(part,v,c)
##    local noc,pv,nv,cv;
##
##    noc:=Length(part[firsts]);
##    pv:=part[prev][v];
##    nv:=part[next][v];
##    cv:=part[fvc][v];
##
##    if c<=cv then
##       Error("New color of vertex must be larger than old.");
##       return;
##    fi;
##    if pv=0 then
##       Error("The vertex to be recolored must not be the first of its color class.");
##       return;
##    fi;
##
##    if nv=0 then
##       part[lasts][cv]:=pv;
##    else
##       part[prev][nv]:=pv;
##    fi;
##
##    if c>noc then
##      if c<>noc+1 then
##         Error("The new color must be the number of colors+1.");
##         return;
##      fi;
##      Add(part[firsts],v);
##      part[prev][v]:=0;
##      Add(part[lengths],1);
##    else
##      part[prev][v]:=part[lasts][c];
##      part[lengths][c]:=part[lengths][c]+1;
##      part[next][part[lasts][c]]:=v;
##    fi;
##
##    part[lengths][cv]:=part[lengths][cv]-1;
##    part[next][pv]:=nv;
##    part[next][v]:=0;
##    part[lasts][c]:=v;
##    part[fvc][v]:=c;
## end;
