ReadPackage("coco2p", "lib/highreg.g4");
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
ReadPackage("coco2p", "lib/newsubiso.gi");
ReadPackage("coco2p", "lib/character.gi");
ReadPackage("coco2p", "lib/colorsemiring.gi");
ReadPackage("coco2p", "lib/hashtable.gi");
ReadPackage("coco2p", "lib/nodes.gi");

if TestPackageAvailability("xgap","0")=true then
    ReadPackage("coco2p", "lib/xgap.gi");
fi;

if TestPackageAvailability("francy","0")=true then
    ReadPackage("coco2p","lib/francy.gi");
fi;

#if TestPackageAvailability("grape","0")=true then
#    ReadPackage("coco2p", "lib/srg.g");
#fi;

