
DeclareCategory( "IsCocoPoset", IsObject );
DeclareOperation( "SuccessorsInCocoPoset", [IsCocoPoset, IsPosInt] );   # documented
DeclareOperation( "PredecessorsInCocoPoset", [IsCocoPoset, IsPosInt] ); # documented 
DeclareOperation( "IdealInCocoPoset", [IsCocoPoset, IsPosInt] );        # documented
DeclareOperation( "FilterInCocoPoset", [IsCocoPoset, IsPosInt] );       # documented
DeclareOperation( "MinimalElementsInCocoPoset", [IsCocoPoset, IsSet] ); # documented
DeclareOperation( "MaximalElementsInCocoPoset", [IsCocoPoset, IsSet] ); # documented
DeclareGlobalFunction( "InducedCocoPoset", [IsCocoPoset, IsSet] );      # documented
DeclareGlobalFunction( "CocoPosetByFunctions" );                        # documented
DeclareOperation( "ElementsOfCocoPoset", [IsCocoPoset] );               # documented

