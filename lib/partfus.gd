#############################################################################
##
##  partfus.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for partial fusions 
##
#############################################################################

DeclareCategory( "IsPartialFusion", IsObject );


DeclareOperation( "EmptyPartialFusion", [IsTensor,IsInt] );
DeclareOperation( "ExtendedPartialFusion", [IsPartialFusion, IsGoodSet] );
DeclareProperty( "IsExtendiblePartialFusion", IsPartialFusion );
DeclareOperation( "IsCompatibleWithPart", [IsPartialFusion, IsGoodSet] );
DeclareOperation( "TensorOfPartialFusion", [IsPartialFusion] );
DeclareAttribute( "IsCompletePartialFusion", IsPartialFusion );
DeclareOperation( "FusionFromCompletePartialFusion", [IsPartialFusion ] );


DeclareCategory( "IsPartialFusionOrbit", IsCocoOrbit );
DeclareGlobalFunction( "PartialFusionOrbitNC" );

DeclareCategory( "IsIteratorOfPFOrbits", IsIterator );
DeclareOperation( "IteratorOfPartialFusionOrbits", [IsList] );
DeclareOperation( "AllFusionOrbits", [IsIteratorOfPFOrbits] );

DeclareGlobalFunction( "WLRefinedPartition" );     # undocumented
