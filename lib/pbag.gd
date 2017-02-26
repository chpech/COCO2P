#################################################################
#W  $Id$
##
##  $Log$
##

Revision.pbag_gd :=
  "@(#)$Id$";

#############################################################################
##
##  pbag.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for the Coco partition backtracker
##
#############################################################################

DeclareInfoClass("InfoPbag");
DeclareGlobalVariable("pbagGlobalData", "A record in which all mutable global variables of pbag are stored.");
DeclareGlobalFunction("ShallowCopyPbagObject");
DeclareGlobalFunction("PbagSemiStep");
DeclareGlobalFunction("PbagSemiStepWithGivenHashTable");
DeclareGlobalFunction("RecolorPbagObject");
DeclareGlobalFunction("RecolorPointOfPbagObject");
DeclareGlobalFunction("PbagStabilStep");
DeclareGlobalFunction("PbagSimultaneousStabilStep");
DeclareGlobalFunction("PbagStabil");
DeclareGlobalFunction("PbagSimultaneousStabil");
DeclareGlobalFunction("PbagGetMaxColorClass");
DeclareGlobalFunction("PbagGetMinColorClass");
DeclareGlobalFunction("PbagGetNewColorClass");
DeclareGlobalFunction("PbagFindBase");
DeclareGlobalFunction("PbagFindCosetRep");
DeclareGlobalFunction("PbagCopyStabChainNode");
DeclareGlobalFunction("PbagExtendStabChain");
DeclareGlobalFunction("PbagFindAutGroup");
DeclareGlobalFunction("PbagFindIsomorphism");
DeclareGlobalFunction("PbagFindIsomorphismInGroup");
DeclareGlobalFunction("PbagInitialize");
DeclareGlobalFunction("AutGroupOfPbagObject");
DeclareGlobalFunction("IsomorphismPbagObjects");
DeclareGlobalFunction("IsomorphismPbagObjectsInGroup");
