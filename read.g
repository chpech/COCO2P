

SetInfoHandler(InfoCOCO, 
function( infoclass, level, list )
    local out, fun, s;
    
    out := InfoOutput(infoclass);
    if out = "*Print*" then
        
        if UserPreference("UseColorsInTerminal")=true  then
            Print(TextAttr.(String(level+1)));
        fi;
        
        for s in list do
            Print(s);
        od;
    
        if UserPreference("UseColorsInTerminal")=true  then
            Print(TextAttr.reset);
        fi;
        Print("\c");
    else
        for s in list do
            AppendTo( out, s );
        od;
        AppendTo( out, "\c" );
    fi;
    return;
end);


ReadPackage("coco2p", "lib/graphtypes.g");
ReadPackage("coco2p", "lib/highreg.gi");
ReadPackage("coco2p", "lib/stbc.g4");
ReadPackage("coco2p", "lib/misc.g4");
ReadPackage("coco2p", "lib/redtest.gi");
ReadPackage("coco2p", "lib/pbag.gi");
ReadPackage("coco2p", "lib/queue.gi");
ReadPackage("coco2p", "lib/wlclosure.gi");
ReadPackage("coco2p", "lib/waut.gi");
ReadPackage("coco2p", "lib/cobject.gi");
ReadPackage("coco2p", "lib/groupact.gi");
ReadPackage("coco2p", "lib/tensor.gi");
ReadPackage("coco2p", "lib/colgraph.gi");
ReadPackage("coco2p", "lib/xcgrinv.gi");
ReadPackage("coco2p", "lib/cocoorbit.gi");
ReadPackage("coco2p", "lib/goodsets.gi");
ReadPackage("coco2p", "lib/partgs.gi");
ReadPackage("coco2p", "lib/posets.gi");
ReadPackage("coco2p", "lib/fusion.gi");
ReadPackage("coco2p", "lib/partfus.gi");
ReadPackage("coco2p", "lib/schemesdb.gi");
ReadPackage("coco2p", "lib/linearsolver.gi");
ReadPackage("coco2p", "lib/paramspgs.gi");
ReadPackage("coco2p", "lib/subiso.gi");
ReadPackage("coco2p", "lib/character.gi");
ReadPackage("coco2p", "lib/colorsemiring.gi");
ReadPackage("coco2p", "lib/hashtable.gi");
ReadPackage("coco2p", "lib/nodes.gi");

if IsPackageLoaded("xgap","0")=true then
    ReadPackage("coco2p", "lib/xgap.gi");
fi;

if IsPackageLoaded("francy","0")=true then
    ReadPackage("coco2p","lib/francy.gi");
fi;

