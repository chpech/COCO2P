#
# This file is a script which compiles the package manual.
#
if fail = LoadPackage("AutoDoc", "2022.07.10") then
    Error("AutoDoc version 2022.07.10 or newer is required.");
fi;

AutoDoc( "coco2p", rec(
    autodoc := true,
    #extract_examples := true,
    gapdoc := rec( main := "coco.xml" ),
    scaffold := rec( MainPage := false, TitlePage := false ),
) );
