#############################################################################
##
##  partgs.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for partial good sets
##
#############################################################################

DeclareCategory( "IsPartialGoodSet", IsObject );
DeclareCategory( "IsAsymPartialGoodSet", IsPartialGoodSet );
DeclareCategory( "IsSymPartialGoodSet",  IsPartialGoodSet );

DeclareOperation( "EmptyAsymPartialGoodSet", [IsTensor and IsTensorOfCC] );          # internal
DeclareOperation( "EmptySymPartialGoodSet", [IsTensor and IsTensorOfCC] );           # internal

DeclareOperation( "ExtendedPartialGoodSet", [IsPartialGoodSet, IsPosInt] );                  # internal
DeclareProperty( "IsExtendiblePartialGoodSet", IsPartialGoodSet );                           # internal
DeclareOperation( "DomainOfPartialGoodSet", [IsPartialGoodSet] );                            # internal
DeclareOperation( "IsCompatiblePoint", [IsPartialGoodSet,IsPosInt] );


#DeclareOperation( "TestPartialGoodSet", [IsPartialGoodSet] );                                # internal 

DeclareOperation( "GoodSetFromPartialGoodSet", [IsPartialGoodSet] );
DeclareOperation( "TensorOfPartialGoodSet", [IsPartialGoodSet] );
DeclareOperation( "IMapOfPartialGoodSet", [IsPartialGoodSet] );
DeclareOperation( "IsEmptyPartialGoodSet", [IsPartialGoodSet] );


################################################################################

DeclareCategory( "IsPartialGoodSetOrbit", IsCocoOrbit );
# DeclareOperation( "GoodSetOrbitFromPartialGoodSetOrbit" )
DeclareGlobalFunction( "PartialGoodSetOrbitNC" );


################################################################################

DeclareCategory( "IsIteratorOfPartialGoodSetOrbits", IsIterator );
DeclareOperation( "IteratorOfPartialGoodSetOrbits", [IsPermGroup, IsPartialGoodSet] );                     # internal
DeclareOperation( "AllGoodSetOrbits", [IsIteratorOfPartialGoodSetOrbits] );                  # internal

