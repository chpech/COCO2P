DeclareCategory( "IsCocoOrbit", IsCollection );
DeclareCategoryCollections( "IsCocoOrbit" );


# constructor
DeclareOperation( "ConstructorOfCocoOrbit", [IsCocoOrbit]);
DeclareOperation( "ConstructorOfCocoOrbitNC", [IsCocoOrbit]);


# user operations
DeclareOperation( "CanonicalRepresentativeOfCocoOrbit", [IsCocoOrbit] );
DeclareOperation( "UnderlyingGroupOfCocoOrbit", [IsCocoOrbit] );
DeclareOperation( "StabilizerOfCanonicalRepresentative", [IsCocoOrbit] );
DeclareOperation( "SubOrbitsOfCocoOrbit", [IsPermGroup, IsCocoOrbit] );
DeclareOperation( "SubOrbitsWithInvariantPropertyOfCocoOrbit", [IsPermGroup, IsCocoOrbit, IsFunction] );
DeclareOperation( "OnCocoOrbits", [IsCocoOrbit, IsPerm] );                                                  # undocumented
DeclareOperation( "FirstSubOrbitWithInvariantPropertyOfCocoOrbit", [IsPermGroup, IsCocoOrbit, IsFunction] );
                   

DeclareAttribute( "ActionOfCocoOrbit", IsCocoOrbit );

DeclareCategory( "IsSetOrbit", IsCocoOrbit );
#DeclareCategoryFamily( "IsSetOrbit" ); # the category of families of SetOrbits


DeclareCategory( "IsPartitionOrbit", IsCocoOrbit );
#DeclareCategoryFamily( "IsPartitionOrbit" ); # the category of families of PartitionOrbits



  
  



