############################################
##  $Id: tensor.gd,v 1.0 2008-11-25 22:15:12+01 zeka Exp zeka $
##
##  $Log: tensor.gd,v $
##  Revision 1.0  2008-11-25 22:15:12+01  zeka
##  Initial revision
##
############################################

Revision.tensor_gd :=
  "@(#)$Id: tensor.gd,v 1.0 2008-11-25 22:15:12+01 zeka Exp zeka $";


#############################################################################
##
##  tensor.gd                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declaration for tensors
##
#############################################################################

DeclareCategory("IsTensor", IsCocoObject);
DeclareInfoClass("InfoTensor");


###
### Constructors
###

DeclareGlobalFunction( "DenseTensorFromEntries" );                                                 # documented
DeclareGlobalFunction( "BlockedTensorFromColorReps" );                                             # undocumented


###
### Properties of Tensors
###

DeclareProperty( "IsTensorOfCC", IsTensor );                                                            # documented 
DeclareProperty( "IsCommutativeTensor", IsTensor );                                                     # documented

###
### Operations
###

DeclareOperation( "EntryOfTensor",   [IsTensor, IsPosInt, IsPosInt, IsPosInt] );                        # documented
# DeclareOperation( "CollapsedTensor", [IsTensor, IsList] );
DeclareOperation( "ComplexProduct",                 [IsTensor, IsList,IsList] );                        # documented
DeclareOperation( "StartBlock",                     [IsTensor and IsTensorOfCC, IsPosInt] );            # documented
DeclareOperation( "FinishBlock",                    [IsTensor and IsTensorOfCC, IsPosInt] );            # documented

DeclareSynonym( "IsIsomorphicTensor", IsIsomorphicCocoObject);                                          # documented 
DeclareSynonym( "IsomorphismTensors", IsomorphismCocoObjects);                                          # documented 
DeclareSynonym( "IsIsomorphismOfTensors", IsIsomorphismOfObjects);                                      # documented
DeclareSynonymAttr( "VertexNamesOfTensor", VertexNamesOfCocoObject);                                        # documented 
DeclareSynonym( "IsAutomorphismOfTensor", IsAutomorphismOfObject);                                      # documented


###
### Attributes
###
DeclareSynonymAttr( "OrderOfTensor",                OrderOfCocoObject );                                # documented
DeclareAttribute( "ReflexiveColors",                IsTensor and IsTensorOfCC );                        # documented
DeclareAttribute( "Mates",                          IsTensor and IsTensorOfCC );                        # documented
DeclareAttribute( "OutValencies",                   IsTensor and IsTensorOfCC );                        # documented
DeclareAttribute( "FibreLengths",                   IsTensor and IsTensorOfCC );                        # documented
DeclareAttribute( "ClosedSets",                     IsTensor );                                         # documented


###
### Families of related object types
###
DeclareAttribute( "FusionFamily",                   IsTensor and IsTensorOfCC );
DeclareAttribute( "GoodSetsFamily",                 IsTensor and IsTensorOfCC ); 
KeyDependentOperation( "GoodSetOrbitFamily", IsTensor, IsPermGroup, ReturnTrue );
KeyDependentOperation( "FusionOrbitFamily", IsTensor, IsPermGroup, ReturnTrue );


DeclareGlobalFunction( "ClosureSet" );                                                                  # documented
