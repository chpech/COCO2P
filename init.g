ReadPackage("coco2p", "lib/highreg.gd"); 
ReadPackage("coco2p", "lib/redtest.gd"); # internal
ReadPackage("coco2p", "lib/pbag.gd"); # internal
ReadPackage("coco2p", "lib/queue.gd"); # internal
ReadPackage("coco2p", "lib/wlclosure.gd"); #internal
ReadPackage("coco2p", "lib/cobject.gd"); # documented
ReadPackage("coco2p", "lib/groupact.gd"); #internal
ReadPackage("coco2p", "lib/tensor.gd");   # documented
ReadPackage("coco2p", "lib/cocoorbit.gd"); # documented
ReadPackage("coco2p", "lib/posets.gd"); # documented
ReadPackage("coco2p", "lib/nodes.gd");
ReadPackage("coco2p", "lib/fusion.gd"); # documented
ReadPackage("coco2p", "lib/colgraph.gd"); # documented
ReadPackage("coco2p", "lib/xcgrinv.gd"); #internal
ReadPackage("coco2p", "lib/goodsets.gd"); # documented
ReadPackage("coco2p", "lib/partgs.gd"); # internal
ReadPackage("coco2p", "lib/schemesdb.gd"); # documented
ReadPackage("coco2p", "lib/partfus.gd"); # internal
ReadPackage("coco2p", "lib/waut.gd"); # internal
ReadPackage("coco2p", "lib/newsubiso.gd"); # documented
ReadPackage("coco2p", "lib/character.gd"); # documented
ReadPackage("coco2p", "lib/colorsemiring.gd"); # documented
ReadPackage("coco2p", "lib/hashtable.gd"); # internal

COCOPrint:=ReturnTrue;

DeclareGlobalVariable("GRAPHTYPESCACHE@COCO2P");


if TestPackageAvailability("xgap","0")=true then
    Print("COCO2P: Using XGAP to display posets...\n");

    ReadPackage("coco2p", "lib/xgap.gd"); #documented
elif TestPackageAvailability("jupyterkernel","0")=true then
    if TestPackageAvailability("francy","0")=true then
        Print("COCO2P: Using francy to display posets...\n");
        ReadPackage("coco2p","lib/francy.gd");
    elif IsString(TestPackageAvailability("francy","0")) then
        Print("COCO2P: Load package francy before coco2p in order to be\n",
              "        able to display posets.\n");
    fi;
fi;

if IsString(TestPackageAvailability("singular", "12")) then
  Print("COCO2P: Load package singular before coco2p to speed up\n",
        "        computations of character tables.\n");
fi;

if IsString(TestPackageAvailability("xgap","0")) then
  Print("COCO2P: Load package xgap before coco2p in order to be\n",
        "        able to display posets.\n");
fi;
