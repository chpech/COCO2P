#############################################################################
##
##  newsubiso.gd               COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for SubColorIsomorphism tests and posets
##
#############################################################################
DeclareGlobalFunction( "EmptySymPartialSTCGoodSet" );
DeclareGlobalFunction( "EmptyAsymPartialSTCGoodSet" );
DeclareGlobalVariable( "symmetric" );
DeclareGlobalVariable( "asymmetric" );
DeclareGlobalVariable( "symmetrized" );
DeclareGlobalVariable( "asymmetrized" );

DeclareGlobalFunction( "DegreeInformationOfTensor" );
DeclareGlobalFunction( "STCSearchPartitionsAux" );
DeclareGlobalFunction( "STCSymmetrizeMSetElement" );
DeclareGlobalFunction( "STCUnSymmetrizeMSetElement" );
DeclareGlobalFunction( "STCSearchPartitions" );
DeclareGlobalFunction( "STCFitVectors" );

DeclareGlobalFunction( "STCBoundedNCombinations" );
DeclareGlobalFunction( "STCMergingsMultiset" );
DeclareGlobalFunction( "STCSolution2Types" );
DeclareGlobalFunction( "STCAugmentedSymType" );

DeclareCategory("IsSubColorIsomorphismPoset", IsCocoPoset);
DeclareOperation( "OrbitsOfColorIsomorphicFusions", [IsColorGraph, IsColorGraph] );   # was ColorIsomorphicFusions
DeclareGlobalFunction( "SubColorIsomorphismPoset" );
