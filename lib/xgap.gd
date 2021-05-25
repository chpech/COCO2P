#############################################################################
##
##  xgap.gd                      COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations of the xgap interface
##
#############################################################################

DeclareFilter( "IsGraphicCocoPoset" );

DeclareOperation( "GraphicCocoPoset", [IsCocoPoset] );

DeclareOperation( "SelectedElements", [ IsGraphicCocoPoset ] );
