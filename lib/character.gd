DeclareGlobalName( "MyValue" ); # undocumented
DeclareGlobalName( "MyRootsOfPoly" ); # undocumented
DeclareGlobalName( "CharacteristicSystem" ); # undocumented
DeclareGlobalName( "SolutionsOfSystem" ); # undocumented
#DeclareGlobalFunction( "MultiplicitiesOfCharacters" ); # undocumented

DeclareOperation( "QPolynomialOrdering", [IsTensor and IsCommutativeTensor and IsTensorOfCC, IsPosInt]); ## documented


DeclareAttribute( "FirstEigenmatrix", IsTensor and IsCommutativeTensor and IsTensorOfCC); ## documented
DeclareAttribute( "SecondEigenmatrix", IsTensor and IsCommutativeTensor and IsTensorOfCC);  ## documented
DeclareAttribute( "TensorOfKreinNumbers", IsTensor and IsCommutativeTensor and IsTensorOfCC); ## documented
DeclareAttribute( "IndexOfPrincipalCharacter", IsTensor and IsCommutativeTensor and IsTensorOfCC); ## documented

DeclareAttribute( "QPolynomialOrderings", IsTensor and IsTensorOfCC); ## documented
DeclareProperty( "IsQPolynomial", IsTensor and IsTensorOfCC ); ## documented

DeclareAttribute( "CharacterTableOfTensor", IsTensor and IsCommutativeTensor and IsTensorOfCC); ## documented
if TestPackageAvailability("singular","12")=true then
    Print("COCO2P: Using Singular for the computation of Groebner-bases...\n");
    ReducedGroebnerBasis@:=SINGULARGBASIS.GroebnerBasis;
else
    ReducedGroebnerBasis@:=ReducedGroebnerBasis;
fi;

