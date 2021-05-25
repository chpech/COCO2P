#############################################################################
##
##  groupact.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declaration for group-actions
##
#############################################################################

DeclareCategory( "IsGroupAction", IsObject);

###
### Constructors
###

DeclareGlobalFunction( "GroupAction" );


###
### Operations
###

DeclareOperation( "UnderlyingGroupOfGroupAction",     [IsGroupAction] );
DeclareOperation( "InducedGroupOfGroupAction",        [IsGroupAction] );
DeclareOperation( "ActionHomomorphismOfGroupAction",  [IsGroupAction] );
DeclareOperation( "OrbRepsOfGroupAction",             [IsGroupAction] );
DeclareOperation( "DomainOfGroupAction",              [IsGroupAction] );
DeclareOperation( "DegreeOfGroupAction",              [IsGroupAction] );
DeclareOperation( "RepresentativeWordOfGroupAction",  [IsGroupAction, IsPosInt] );
DeclareGlobalFunction( "ApplyRepWord" );
DeclareOperation( "OrbitNumber",                      [IsGroupAction, IsPosInt] );
