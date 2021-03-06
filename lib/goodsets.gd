#############################################################################
##
##  goodsets.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for good sets
##
#############################################################################




################################################################################


DeclareCategory( "IsGoodSet", IsCocoObject );

DeclareGlobalFunction( "BuildGoodSet" );                                       # documented

DeclareOperation( "TensorOfGoodSet", [IsGoodSet] );                            # documented
DeclareOperation( "OnGoodSets", [IsGoodSet, IsPerm] );                         # undocumented
DeclareOperation( "PartitionOfGoodSet" , [IsGoodSet] );                        # documented

################################################################################

DeclareCategory( "IsGoodSetOrbit", IsSetOrbit );

DeclareGlobalFunction( "GoodSetOrbit" );                                       # documented
DeclareGlobalFunction( "GoodSetOrbitNC" );                                     # undocumented
DeclareOperation( "HomogeneousGoodSetOrbits", [IsTensor and IsTensorOfCC] );   # documented
DeclareAttribute( "HomogeneousSymGoodSetOrbits", IsTensor and IsTensorOfCC );  # documented
DeclareAttribute( "HomogeneousAsymGoodSetOrbits", IsTensor and IsTensorOfCC ); # documented
