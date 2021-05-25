DeclareGlobalFunction( "MyValue" );                                            # undocumented
DeclareGlobalFunction( "MyRootsOfPoly" );                                      # undocumented
DeclareGlobalFunction( "CharacteristicSystem" );                               # undocumented
DeclareGlobalFunction( "SolutionsOfSystem" );                                  # undocumented
#DeclareGlobalFunction( "MultiplicitiesOfCharacters" );                         # undocumented

DeclareOperation( "QPolynomialOrdering", [IsTensor and IsCommutativeTensor and IsTensorOfCC, IsPosInt]);


DeclareAttribute( "FirstEigenmatrix", IsTensor and IsCommutativeTensor and IsTensorOfCC);   # to be documented!
DeclareAttribute( "SecondEigenmatrix", IsTensor and IsCommutativeTensor and IsTensorOfCC);  # to be documented!
DeclareAttribute( "TensorOfKreinNumbers", IsTensor and IsCommutativeTensor and IsTensorOfCC); # to be documented!
DeclareAttribute( "IndexOfPrincipalCharacter", IsTensor and IsCommutativeTensor and IsTensorOfCC); # to be documented

DeclareAttribute( "QPolynomialOrderings", IsTensor and IsTensorOfCC); # to be documented

DeclareAttribute( "CharacterTableOfTensor", IsTensor and IsCommutativeTensor and IsTensorOfCC); # documented
if TestPackageAvailability("singular","12")=true then
    Print("COCO2P: Using Singular for the computation of Groebner-bases...\n");
    ReducedGroebnerBasis@:=SINGULARGBASIS.GroebnerBasis;
else
    ReducedGroebnerBasis@:=ReducedGroebnerBasis;
fi;

