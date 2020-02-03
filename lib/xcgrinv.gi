#############################################################################
##
##  xcgrinv.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementationof  the invariant of recolored color graphs (xcgr)
##
#############################################################################


InstallGlobalFunction(ChangeColoringOfXCgr,
function(xcgr,m)
   xcgr.merging:=m;
end);

InstallGlobalFunction(RowOfXCgrObject,
function(obj,v)
   return RowOfCgrObject(obj.T,v);
end);

InstallGlobalFunction(BuildXCgr,
function(W,merging)
    local obj,T;

    T:=rec(      T := W,
           merging := merging);
    return T;
end);


InstallGlobalFunction(BuildXCgrObject,
function(arg)
    local obj,T,cgr,merging,g,xcgr;

    if Length(arg)=1 and IsRecord(arg[1]) then
       xcgr:=arg[1];
       cgr:=xcgr.T;
       g:=KnownGroupOfAutomorphisms(cgr);
    else
       cgr:=arg[1];
       if IsBound(arg[2]) then
           merging:=arg[2];
       else
           merging:=[1..Rank(cgr)];
       fi;
       g:= KnownGroupOfAutomorphisms(cgr);
       xcgr:=BuildXCgr(cgr,merging);
    fi;

    obj:=rec(
               T := xcgr,
               v := Order(cgr),
             ncp := 1,
             fvc := List([1..OrderOfColorGraph(cgr)], x->1),
             fcv := [[1..OrderOfColorGraph(cgr)]],
               S := [],
              ST := [],
       stabChain := StabChainMutable(g));
    return obj;
end);



InstallGlobalFunction(TestIsomorphismXCgr,
function(TRec1, TRec2, perm)
    local i,j,row1,row2,W1,W2,m1,m2;

    m1:=TRec1.T.merging;
    m2:=TRec2.T.merging;

    for i in [1..TRec1.v] do
        row1:=Permuted(RowOfXCgrObject(TRec1, i),perm);
        row2:=RowOfXCgrObject(TRec2, i^perm);
        for j in [1..Length(row1)] do
            if m1[row1[j]]<>m2[row2[j]] then
                return false;
            fi;
        od;
    od;
    return true;
end);

InstallGlobalFunction(TestAutomorphismXCgr,
function(TRec1, perm)
    return TestIsomorphismXCgr(TRec1,TRec1,perm);
end);


InstallGlobalFunction(XCgrInv,
function(obj,v)
    local inv,W,m,row;

    m:=obj.T.merging;
    row:=RowOfXCgrObject(obj,v);
    inv:=List(obj.ST, y->m[row[y]]);
    Add(inv, obj.fvc[v]);
    return inv;
end);



InstallGlobalFunction(XCgrInvHash,
function(inv)
    return inv*[1..Length(inv)];
end);
