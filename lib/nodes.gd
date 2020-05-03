DeclareCategory( "IsCocoNode", IsObject );
DeclareOperation( "IndexOfCocoNode", [IsCocoNode] );
DeclareOperation( "ShapeOfCocoNode", [IsCocoNode] );
DeclareOperation( "LevelOfCocoNode", [IsCocoNode] );
DeclareOperation( "NewCocoNode", [IsCocoPoset, IsPosInt] );
DeclareOperation( "NodeInfoString", [IsCocoNode] );
DeclareOperation( "ComputeInfo", [IsCocoNode, IsString] );
DeclareOperation( "ComputeAllInfos", [IsCocoNode] );
DeclareOperation( "UpdateInfoInCocoNode", [IsCocoNode,IsString] );


BindGlobal( "infoOptions@", rec(disabled:=["Aut:"]));
