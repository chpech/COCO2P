#############################################################################
##
##  fusion.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for the fusion-datatype
##
#############################################################################

DeclareCategory( "IsFusionOfTensor", IsObject );

DeclareGlobalFunction( "FusionFromPartition" );                          # documented
DeclareGlobalFunction( "FusionFromPartitionNC" );                        # undocumented
DeclareGlobalFunction( "FusionFromPartitionAndBaseNC" );                 # undocumented
DeclareGlobalFunction( "RefineFuseAndFilterGoodSetOrbits" );              # undocumented
DeclareGlobalFunction( "FusionOrbitsFromGoodSetOrbits" );  # undocumented ?


DeclareOperation( "PartitionOfFusion", [IsFusionOfTensor] );              # documented
DeclareOperation( "TensorOfFusion", [IsFusionOfTensor] );                 # documented
DeclareOperation( "OnFusions", [IsFusionOfTensor, IsPerm] );              # undocumented

DeclareAttribute("RankOfFusion", IsFusionOfTensor);                       # documented
DeclareAttribute("BaseOfFusion", IsFusionOfTensor);                       # documented
DeclareAttribute("AsPartition", IsFusionOfTensor);                        # documented
DeclareAttribute( "HomogeneousFusionOrbits", IsTensor and IsTensorOfCC ); # documented

DeclareCategory( "IsFusionOrbit", IsPartitionOrbit );
DeclareGlobalFunction( "FusionOrbitNC" );                                 # undocumented
DeclareGlobalFunction( "FusionOrbit" );                                   # documented


DeclareGlobalFunction( "ShortLexSorted" );                                # undocumented
DeclareGlobalFunction( "WLRefinedPartition" );     # undocumented
DeclareGlobalFunction( "IsCompatibleGS" );
