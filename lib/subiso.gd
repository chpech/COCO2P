#############################################################################
##
##  subiso.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for SubColorIsomorphism tests and posets
##
#############################################################################


DeclareCategory("IsSubColorIsomorphismPoset", IsCocoPoset);
DeclareOperation( "OrbitsOfColorIsomorphicFusions", [IsColorGraph, IsColorGraph] );   # was ColorIsomorphicFusions
DeclareGlobalFunction( "SubColorIsomorphismPoset" );
