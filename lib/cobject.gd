############################################
##  $Id: cobject.gd,v 1.0 2008-12-06 10:07:14+01 zeka Exp zeka $
##
##  $Log: cobject.gd,v $
##  Revision 1.0  2008-12-06 10:07:14+01  zeka
##  Initial revision
##
############################################

Revision.cobject_gd :=
  "@(#)$Id: cobject.gd,v 1.0 2008-12-06 10:07:14+01 zeka Exp zeka $";


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

DeclareOperation( "PbagInvariant",                [IsCocoObject] );
DeclareOperation( "NewPbagObject",                [IsCocoObject] );
DeclareOperation( "IsIsomorphismOfObjects",       [IsCocoObject, IsCocoObject, IsPerm] ); # doc for cgr, tensor
DeclareOperation( "KnownGroupOfAutomorphisms",    [IsCocoObject] ); 
DeclareOperation( "SetKnownGroupOfAutomorphisms", [IsCocoObject,IsPermGroup] );
DeclareOperation( "SetKnownGroupOfAutomorphismsNC", [IsCocoObject, IsPermGroup] );
DeclareOperation( "VertexNamesOfCocoObject",      [IsCocoObject] );
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
