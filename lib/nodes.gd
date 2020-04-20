DeclareCategory( "IsCocoNode", IsObject );
DeclareOperation( "IndexOfCocoNode", [IsCocoNode] );
DeclareOperation( "ShapeOfCocoNode", [IsCocoNode] );
DeclareOperation( "LevelOfCocoNode", [IsCocoNode] );
DeclareOperation( "NewCocoNode", [IsCocoPoset, IsPosInt] );
DeclareOperation( "NodeInfoString", [IsCocoNode] );
BindGlobal( "infoOptions@", rec(disabled:=["Aut:"]));
