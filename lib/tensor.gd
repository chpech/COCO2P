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

DeclareGlobalFunction( "DenseTensorFromEntries" ); ## documented
DeclareGlobalFunction( "TensorFromColorReps" ); # undocumented



###
### Properties of Tensors
###

DeclareProperty( "IsTensorOfCC", IsTensor ); ## documented
DeclareProperty( "IsCommutativeTensor", IsTensor ); ## documented
DeclareProperty( "IsHomogeneousTensor", IsTensor ); ## documented
DeclareProperty( "IsPPolynomial", IsTensor and IsTensorOfCC ); ## documented


###
### Operations
###

DeclareOperation( "EntryOfTensor", [IsTensor, IsPosInt, IsPosInt, IsPosInt] ); ## documented
DeclareOperation( "ComplexProduct", [IsTensor, IsList,IsList] ); ## documented
DeclareOperation( "StartBlock", [IsTensor and IsTensorOfCC, IsPosInt] ); ## documented
DeclareOperation( "FinishBlock", [IsTensor and IsTensorOfCC, IsPosInt] ); ## documented
DeclareOperation( "BlockOfTensor", [IsTensor and IsTensorOfCC, IsPosInt, IsPosInt] ); ## document 

DeclareSynonym( "IsIsomorphicTensor", IsIsomorphicCocoObject); ## documented
DeclareSynonym( "IsomorphismTensors", IsomorphismCocoObjects); ## documented
DeclareSynonym( "IsIsomorphismOfTensors", IsIsomorphismOfObjects); ## documented
DeclareSynonymAttr( "VertexNamesOfTensor", VertexNamesOfCocoObject); ## documented
DeclareSynonym( "IsAutomorphismOfTensor", IsAutomorphismOfObject); ## documented
DeclareOperation( "IsClosedSet", [IsTensor, IsList] ); ## documented
DeclareOperation( "PPolynomialOrdering", [IsTensor and IsTensorOfCC, IsPosInt]); ## documented



###
### Attributes
###
DeclareSynonymAttr( "OrderOfTensor",                OrderOfCocoObject ); ## documented
DeclareAttribute( "ReflexiveColors",                IsTensor and IsTensorOfCC ); ## documented
DeclareAttribute( "Mates",                          IsTensor and IsTensorOfCC ); ## documented
DeclareAttribute( "OutValencies",                   IsTensor and IsTensorOfCC ); ## documented
DeclareAttribute( "FibreLengths",                   IsTensor and IsTensorOfCC ); ## documented
DeclareAttribute( "ClosedSets",                     IsTensor ); ## documented
DeclareAttribute( "PPolynomialOrderings",           IsTensor and IsTensorOfCC ); ## !document!


###
### Families of related object types
###
DeclareAttribute( "FusionFamily",                   IsTensor and IsTensorOfCC );
DeclareAttribute( "GoodSetsFamily",                 IsTensor and IsTensorOfCC );
KeyDependentOperation( "GoodSetOrbitFamily", IsTensor, IsPermGroup, ReturnTrue );
KeyDependentOperation( "FusionOrbitFamily", IsTensor, IsPermGroup, ReturnTrue );


DeclareGlobalFunction( "ClosureSet" ); ## documented

###
### auxiliary functions
###
DeclareGlobalFunction( "NewPbagObjectForTensorOfCC"); # undocumented
DeclareGlobalFunction( "NewPbagObjectForDenseTensor"); # undocumented



# NumberOfFibres ## documented
# IsHomogeneous ## documented
# IsPrimitive ## documented
# \[\] ## documented
