DeclareGlobalFunction("MatrixFromCode@COCO2P");
DeclareGlobalFunction("CodeFromMatrix@COCO2P");

DeclareGlobalFunction("ReadG7File@COCO2P");

DeclareGlobalFunction("AllAssociationSchemes"); ## documented
DeclareGlobalFunction("SmallAssociationScheme"); ## documented
DeclareGlobalFunction("NumberAssociationSchemes"); ## documented
DeclareGlobalFunction("SmallAssociationSchemesAvailable"); ## documented


DeclareGlobalFunction("AllCoherentConfigurations"); ## documented
DeclareGlobalFunction("SmallCoherentConfiguration"); ## documented
DeclareGlobalFunction("NumberCoherentConfigurations"); ## documented
DeclareGlobalFunction("SmallCoherentConfigurationsAvailable"); ## documented
smallAssociationSchemesAvailable@:=Immutable(Difference([1..40],[1,2,35,36,37,39,40]));
smallCoherentConfigurationsAvailable@:=Immutable([2..15]);
