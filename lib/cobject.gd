#############################################################################
##
##  cobject.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declaration for coco-objects (abstract class for combinatorial objects)
##
#############################################################################


DeclareCategory("IsCocoObject", IsObject);

###
### Operations
###

DeclareOperation( "PbagInvariant",                [IsCocoObject, IsCocoObject] );
DeclareOperation( "NewPbagObject",                [IsCocoObject] );
DeclareOperation( "NewPbagObjects",               [IsCocoObject, IsCocoObject] );
DeclareOperation( "IsIsomorphismOfObjects",       [IsCocoObject, IsCocoObject, IsPerm] ); # doc for cgr, tensor
DeclareOperation( "KnownGroupOfAutomorphisms",    [IsCocoObject] );
DeclareOperation( "SetKnownGroupOfAutomorphisms", [IsCocoObject,IsPermGroup] );
DeclareOperation( "SetKnownGroupOfAutomorphismsNC", [IsCocoObject, IsPermGroup] );
DeclareOperation( "IsomorphismCocoObjects",       [IsCocoObject, IsCocoObject] );
DeclareOperation( "IsIsomorphicCocoObject",       [IsCocoObject, IsCocoObject] );
DeclareOperation( "IsomorphismCocoObjectsInGroup", [IsPermGroup, IsCocoObject, IsCocoObject] );
DeclareOperation( "IsAutomorphismOfObject",       [IsCocoObject, IsPerm] );


DeclareGlobalFunction( "PbagInvariantWithInvariantPartition" );
DeclareGlobalFunction( "NewPbagObjectWithInvariantPartition" );


###
### Attributes
###

DeclareAttribute( "OrderOfCocoObject",         IsCocoObject );
DeclareAttribute( "KnownGroups",               IsCocoObject, "mutable" );
DeclareAttribute( "AutGroupOfCocoObject",      IsCocoObject );
DeclareAttribute( "VertexNamesOfCocoObject",   IsCocoObject );
