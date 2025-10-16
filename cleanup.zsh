#!/bin/zsh
cd /Users/pech/Library/Preferences/GAP/pkg/coco2p
touch test.txt~
rm **/*~ 

cd /Users/pech/Library/Preferences/GAP/pkg/coco2p/doc
setopt extended_glob
touch test.txt
rm ^(coco.bib|coco.xml|gapdoc.dtd|gapdoc.rnc|directory_name)
