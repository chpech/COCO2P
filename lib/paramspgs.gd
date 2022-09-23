DeclareGlobalFunction("MatrixAndBoundsSym");

DeclareGlobalFunction("MatrixAndBoundsAsym");

DeclareOperation("EmptySymPartialGoodSetWithParams", [IsTensor and IsTensorOfCC, IsList, IsList, IsPosInt, IsInt] );

DeclareOperation("EmptyAsymPartialGoodSetWithParams", [IsTensor and IsTensorOfCC, IsList, IsList, IsPosInt, IsInt] );

DeclareOperation( "HomogeneousSymGoodSetOrbitsWithParameters", [IsTensor and IsTensorOfCC, IsPosInt, IsInt] );   # undocumented

DeclareOperation( "HomogeneousAsymGoodSetOrbitsWithParameters", [IsTensor and IsTensorOfCC, IsPosInt, IsInt] );   # undocumented
