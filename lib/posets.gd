#############################################################################
##
##  posets.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for coco posets         
##
#############################################################################

DeclareCategory( "IsCocoPoset", IsObject );
DeclareOperation( "SuccessorsInCocoPoset", [IsCocoPoset, IsPosInt] );   # documented
DeclareOperation( "PredecessorsInCocoPoset", [IsCocoPoset, IsPosInt] ); # documented 
DeclareOperation( "IdealInCocoPoset", [IsCocoPoset, IsPosInt] );        # documented
DeclareOperation( "FilterInCocoPoset", [IsCocoPoset, IsPosInt] );       # documented
DeclareOperation( "MinimalElementsInCocoPoset", [IsCocoPoset, IsSet] ); # documented
DeclareOperation( "MaximalElementsInCocoPoset", [IsCocoPoset, IsSet] ); # documented
DeclareConstructor( "InducedCocoPoset", [IsCocoPoset, IsCocoPoset, IsSet] );           # documented
DeclareGlobalFunction( "CocoPosetByFunctions" );                        # documented
DeclareOperation( "ElementsOfCocoPoset", [IsCocoPoset] );               # documented

