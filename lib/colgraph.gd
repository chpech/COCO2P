############################################
##  $Id: colgraph.gd,v 1.0 2008-11-27 15:32:16+01 zeka Exp zeka $
##
##  $Log: colgraph.gd,v $
##  Revision 1.0  2008-11-27 15:32:16+01  zeka
##  Initial revision
##
##
############################################

Revision.colgraph_gd :=
  "@(#)$Id: colgraph.gd,v 1.0 2008-11-27 15:32:16+01 zeka Exp zeka $";

#############################################################################
##
##  colgraph.gd                  COCO package                      
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declaration for color graphs
##
#############################################################################


DeclareCategory( "IsColorGraph", IsCocoObject );


###
### Constructors
###

DeclareGlobalFunction("ColorGraphByOrbitals");									# documented
DeclareGlobalFunction("ColorGraph");                                                                            # documented
DeclareGlobalFunction("ColorGraphByMatrix");                                                                    # documented
DeclareGlobalFunction("CyclotomicColorGraph");                                                                  # documented
DeclareGlobalFunction("ClassicalCompleteAffineScheme");                                                         # documented
DeclareGlobalFunction("JohnsonScheme");                                                                         # documented
DeclareGlobalFunction("ColorGraphByWLStabilization" );                                                          # documented
DeclareGlobalFunction("BIKColorGraph" );                                                                        # still undocumented
DeclareGlobalFunction("IvanovColorGraph" );                                                                     # still undocumented


###
### Properties
###

DeclareProperty( "IsWLStableColorGraph",   IsColorGraph );                                                           # documented
DeclareProperty( "IsHomogeneous",          IsColorGraph );                                                           # documented
DeclareProperty( "IsSchurian",             IsColorGraph and IsWLStableColorGraph );                                  # documented
DeclareProperty( "IsUndirectedColorGraph", IsColorGraph );                                                           # documented

####
#### Operations
####

DeclareOperation( "ColorGraphByFusion",                      [IsColorGraph, IsFusionOfTensor] );                     # documented
DeclareOperation( "ArcColorOfColorGraph",                    [IsColorGraph, IsPosInt, IsPosInt] );                   # documented
DeclareOperation( "RowOfColorGraph",                         [IsColorGraph, IsPosInt] );                             # documented
DeclareOperation( "ColumnOfColorGraph",                      [IsColorGraph, IsPosInt] );                             # documented
DeclareOperation( "Fibres",                                  [IsColorGraph] );                                       # documented
DeclareOperation( "Neighbors",                               [IsColorGraph, IsPosInt, IsList] );                     # documented
DeclareOperation( "AdjacencyMatrix",                         [IsColorGraph] );                                       # documented
DeclareOperation( "ColorRepresentative",                     [IsColorGraph, IsPosInt] );                             # documented
DeclareOperation( "LocalIntersectionArray",                  [IsColorGraph, IsPosInt, IsPosInt] );                   # documented
DeclareOperation( "QuotientColorGraph",                      [IsColorGraph, IsSet] );                                # documented
DeclareOperation( "ColorNames",                              [IsColorGraph] );                                       # documented
DeclareOperation( "InducedSubColorGraph",                    [IsColorGraph, IsList] );                               # documented
DeclareOperation( "DirectProductColorGraphs",                 [IsColorGraph, IsColorGraph] );                         # documented
DeclareOperation( "WreathProductColorGraphs",                 [IsColorGraph, IsColorGraph] );                         # documented


DeclareOperation( "PartitionClosedSet",                      [IsColorGraph and IsWLStableColorGraph and IsHomogeneous, IsList] ); # documented

DeclareOperation( "KnownGroupOfAlgebraicAutomorphisms",      [IsColorGraph and IsWLStableColorGraph] );              # documented
DeclareOperation( "KnownGroupOfColorAutomorphisms",          [IsColorGraph] );                                       # documented
DeclareOperation( "SetKnownGroupOfColorAutomorphismsNC",     [IsColorGraph, IsPermGroup] );                          # undocumented
DeclareOperation( "SetKnownGroupOfAlgebraicAutomorphismsNC", [IsColorGraph and IsWLStableColorGraph, IsPermGroup] ); # undocumented
DeclareOperation( "LiftToColorAutomorphism",                 [IsColorGraph, IsPerm] );                               # documented
DeclareOperation( "LiftToColorIsomorphism",                  [IsColorGraph, IsColorGraph, IsPerm] );                 # documented
DeclareOperation( "ColorIsomorphismColorGraphs",             [IsColorGraph, IsColorGraph] );                         # for WL-stable; documented
DeclareOperation( "IsColorIsomorphicColorGraph",             [IsColorGraph, IsColorGraph] );                         # for WL-stable; documented
DeclareSynonym( "IsIsomorphicColorGraph", IsIsomorphicCocoObject);                                                   # documented
DeclareSynonym( "IsomorphismColorGraphs", IsomorphismCocoObjects);                                                   # documented
DeclareSynonym( "IsIsomorphismOfColorGraphs", IsIsomorphismOfObjects);                                               # documented
DeclareSynonymAttr( "VertexNamesOfColorGraph", VertexNamesOfCocoObject);                                                 # documented
DeclareSynonym( "IsAutomorphismOfColorGraph", IsAutomorphismOfObject);                                               # documented


if TestPackageAvailability("grape","0")=true then
    DeclareOperation( "BaseGraphOfColorGraph",                   [IsColorGraph, IsPosInt] );                         # only declare if <grape> is loaded; documented
fi;



###
### Attributes
###

DeclareSynonymAttr( "OrderOfColorGraph", OrderOfCocoObject );                                                        # documented
DeclareAttribute( "RankOfColorGraph",               IsColorGraph );                                                  # documented
DeclareAttribute( "StructureConstantsOfColorGraph", IsColorGraph and IsWLStableColorGraph );                         # documented
DeclareAttribute( "ColorMates",                     IsColorGraph and IsWLStableColorGraph );                         # documented
DeclareAttribute( "NumberOfFibres",                 IsColorGraph );                                                  # documented

DeclareAttribute( "ColorAutomorphismGroup",         IsColorGraph );                                                  # for WL-stable; documented
DeclareAttribute( "ColorAutomorphismGroupOnColors", IsColorGraph );                                                  # for WL-stable; documented
DeclareAttribute( "AlgebraicAutomorphismGroup",     IsColorGraph and IsWLStableColorGraph );                         # documented

###
### Private functions, for internal use
###

DeclareGlobalFunction( "RowOfCgrObject" );                                                                           # undocumented

