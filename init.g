ReadPackage("coco2p", "lib/redtest.gd"); # internal
ReadPackage("coco2p", "lib/pbag.gd"); # internal
ReadPackage("coco2p", "lib/queue.gd"); # internal
ReadPackage("coco2p", "lib/wlclosure.gd"); #internal
ReadPackage("coco2p", "lib/cobject.gd"); # documented
ReadPackage("coco2p", "lib/groupact.gd"); #internal
ReadPackage("coco2p", "lib/tensor.gd");   # documented
ReadPackage("coco2p", "lib/cocoorbit.gd"); # documented
ReadPackage("coco2p", "lib/fusion.gd"); # documented
ReadPackage("coco2p", "lib/colgraph.gd"); # documented
ReadPackage("coco2p", "lib/xcgrinv.gd"); #internal
ReadPackage("coco2p", "lib/goodsets.gd"); # documented
ReadPackage("coco2p", "lib/schemesdb.gd"); # documented
ReadPackage("coco2p", "lib/posets.gd"); # documented
ReadPackage("coco2p", "lib/waut.gd"); # internal
ReadPackage("coco2p", "lib/subiso.gd"); # documented
ReadPackage("coco2p", "lib/character.gd"); # documented
ReadPackage("coco2p", "lib/colorsemiring.gd"); # documented
ReadPackage("coco2p", "lib/hashtable.gd"); # internal
COCOPrint:=ReturnTrue;

if TestPackageAvailability("xgap","0")=true then
    Print("COCO2P: Using XGAP to display posets...\n");
    
    ReadPackage("coco2p", "lib/xgap.gd"); #documented
fi;

