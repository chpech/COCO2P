############################################
##  $Id$
##
##  $Log$
##
############################################

Revision.goosets_gd :=
  "@(#)$Id$";


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

DeclareCategory( "IsGoodSetCandidate", IsObject );
DeclareCategory( "IsAsymGoodSetCandidate", IsGoodSetCandidate );
DeclareCategory( "IsSymGoodSetCandidate",  IsGoodSetCandidate );


# DeclareOperation( "EmptyAsymGoodSetCandidate", [IsTensor and IsTensorOfCC, IsList, IsList] );
# DeclareOperation( "EmptySymGoodSetCandidate", [IsTensor and IsTensorOfCC, IsList] );
DeclareGlobalFunction( "EmptyAsymGoodSetCandidate" );  # for inhomogeneous tensors of CC
DeclareGlobalFunction( "EmptySymGoodSetCandidate" );   # for inhomogeneous tensors of CC
DeclareGlobalFunction( "EmptyAsymGoodSetCandHom" );    # for homogeneous tensors of CC
DeclareGlobalFunction( "EmptySymGoodSetCandHom" );     # for homogeneous tensors of CC
DeclareGlobalFunction( "ExtendSymGSCand" );
DeclareGlobalFunction( "ExtendAsymGSCand" );
DeclareGlobalFunction( "GetNormalizingPermutationForAsymCandidate" );
DeclareGlobalFunction( "GetNormalizingPermutationForSymCandidate" );


DeclareOperation( "ExtendedCandidate", [IsGoodSetCandidate, IsPosInt] );
DeclareProperty( "IsExtendibleCandidate", IsGoodSetCandidate );
DeclareOperation( "NormalizedDomainOfCandidate", [IsGoodSetCandidate] );
DeclareOperation( "TestCandidate", [IsGoodSetCandidate] );
DeclareAttribute( "NormalizedSetOfCandidate", IsGoodSetCandidate );
DeclareOperation( "TensorOfCandidate", [IsGoodSetCandidate] );
DeclareOperation( "SetOfCandidate", [IsGoodSetCandidate] );
DeclareOperation( "NormalizingPermutationOfCandidate", [IsGoodSetCandidate] );



################################################################################


DeclareCategory( "IsGoodSet", IsCocoObject );

DeclareGlobalFunction( "BuildGoodSet" );                                       # documented

DeclareOperation( "TensorOfGoodSet", [IsGoodSet] );                            # documented
DeclareOperation( "OnGoodSets", [IsGoodSet, IsPerm] );                         # undocumented
DeclareOperation( "PartitionOfGoodSet" , [IsGoodSet]);                         # documented

################################################################################

DeclareCategory( "IsGoodSetOrbit", IsSetOrbit );
DeclareGlobalFunction( "SUBHomAsymGSReps" );                                   # undocumented
DeclareGlobalFunction( "SUBHomSymGSReps" );                                    # undocumented
DeclareGlobalFunction( "GoodSetOrbit" );                                       # documented
DeclareGlobalFunction( "GoodSetOrbitNC" );                                     # undocumented
DeclareAttribute( "HomogeneousGoodSetOrbits", IsTensor and IsTensorOfCC );     # documented

