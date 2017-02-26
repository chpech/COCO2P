DeclareCategory("IsElementOfColorSemiring", 
        IsMultiplicativeElementWithOne and
        IsMultiplicativeElementWithZero and 
        IsAdditiveElementWithZero);
DeclareCategoryFamily("IsElementOfColorSemiring"); # the category of families of elements of colorsemirings 
DeclareCategoryCollections("IsElementOfColorSemiring");
DeclareCategoryCollections("IsElementOfColorSemiringCollection");

DeclareCategory("IsColorSemiring", 
        IsAdditiveMagmaWithZero 
        and IsMagmaWithOne 
        and IsAssociative 
        and IsDistributive );

DeclareAttribute( "GeneratorsOfColorSemiring", IsColorSemiring );   # documented
DeclareGlobalFunction("ColorSemiring");                             # documented 
DeclareOperation("ColorSemiringElement", [IsElementOfColorSemiringFamily, IsList]);
DeclareGlobalFunction("AsElementOfColorSemiring");                  # documented
