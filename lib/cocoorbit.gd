DeclareCategory( "IsCocoOrbit", IsCollection );
DeclareCategoryCollections( "IsCocoOrbit" );


# user operations
DeclareOperation( "CanonicalRepresentativeOfCocoOrbit", [IsCocoOrbit] );
DeclareOperation( "UnderlyingGroupOfCocoOrbit", [IsCocoOrbit] );
DeclareOperation( "StabilizerOfCanonicalRepresentative", [IsCocoOrbit] );
DeclareOperation( "SubOrbitsOfCocoOrbit", [IsPermGroup, IsCocoOrbit] );
DeclareOperation( "SubOrbitsWithInvariantPropertyOfCocoOrbit", [IsPermGroup, IsCocoOrbit, IsFunction] );
DeclareOperation( "OnCocoOrbits", [IsCocoOrbit, IsPerm] );                                                  # undocumented

DeclareAttribute( "ActionOfCocoOrbit", IsCocoOrbit );

DeclareCategory( "IsSetOrbit", IsCocoOrbit );
DeclareCategoryFamily( "IsSetOrbit" ); # the category of families of SetOrbits

DeclareOperation( "SetOrbitNC", [IsSetOrbitFamily, IsPermGroup, IsSSortedList] ); 
DeclareOperation( "SetOrbit", [IsSetOrbitFamily, IsPermGroup, IsSSortedList] );


DeclareCategory( "IsPartitionOrbit", IsCocoOrbit );
DeclareCategoryFamily( "IsPartitionOrbit" ); # the category of families of PartitionOrbits



  
  



