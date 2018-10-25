#############################################################################
##
##  wlclosure.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for the Weisfeiler-Leman algorithm that works inside
##  of a given coherent configuration
##
#############################################################################

#constructors
DeclareGlobalFunction("WLBuildAsymGoodSetPartition");
DeclareGlobalFunction("WLBuildSymGoodSetPartition");
DeclareGlobalFunction("WLBuildTrivialPartition");
DeclareGlobalFunction("WLBuildPartition");
DeclareGlobalFunction("WLShallowCopyStablePartition");
DeclareGlobalFunction("WLBuildFixedPartition");
DeclareGlobalFunction("WLIsStablePartition");


DeclareGlobalFunction("WLPartitionClass");
DeclareGlobalFunction("WLSetToTestFlag");
DeclareGlobalFunction("WLClearToTestFlag");
DeclareGlobalFunction("WLIsToTest");
DeclareGlobalFunction("WLToTestQueueAdd");
DeclareGlobalFunction("WLToTestQueueRemove");
DeclareGlobalFunction("WLSetInstabilFlag");
DeclareGlobalFunction("WLClearInstabilFlag");
DeclareGlobalFunction("WLIsInstabil");
DeclareGlobalFunction("WLInstabilQueueAdd");
DeclareGlobalFunction("WLInstabilQueueRemove");
DeclareGlobalFunction("WLRepartition");
DeclareGlobalFunction("WLIsAntiSymmetricSet");
DeclareGlobalFunction("WLStabil");
DeclareGlobalFunction("WLIsReflexiveSet");
