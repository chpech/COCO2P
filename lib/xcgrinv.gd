#############################################################################
##
##  xcgrinv.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for the invariant of recolored color graphs (xcgr)
##
#############################################################################

DeclareGlobalFunction("ChangeColoringOfXCgr");
DeclareGlobalFunction("RowOfXCgrObject");
DeclareGlobalFunction("BuildXCgr");
DeclareGlobalFunction("BuildXCgrObject");
DeclareGlobalFunction("TestIsomorphismXCgr");
DeclareGlobalFunction("TestAutomorphismXCgr");
DeclareGlobalFunction("XCgrInv");
DeclareGlobalFunction("XCgrInvHash");
BindGlobal("NOCOLOR",0);
BindGlobal("XCgrInvariant", rec(   finv := XCgrInv,
                                hashinv := XCgrInvHash,
                                   test := TestIsomorphismXCgr,
                                autTest := TestAutomorphismXCgr));
