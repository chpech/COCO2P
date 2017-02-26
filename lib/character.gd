DeclareGlobalFunction( "MyValue" );                                            # undocumented
DeclareGlobalFunction( "MyRootsOfPoly" );                                      # undocumented
DeclareGlobalFunction( "CharacteristicSystem" );                               # undocumented
DeclareGlobalFunction( "SolutionsOfSystem" );                                  # undocumented
DeclareGlobalFunction( "MultiplicitiesOfCharacters" );                         # undocumented
DeclareAttribute( "CharacterTableOfTensor", IsTensor and IsCommutativeTensor); # documented
if TestPackageAvailability("singular","12")=true then
    Print("COCO2P: Using Singular for the computation of Groebner-bases...\n");
    ReducedGroebnerBasis@:=SINGULARGBASIS.GroebnerBasis;
else
    ReducedGroebnerBasis@:=ReducedGroebnerBasis;
fi;

