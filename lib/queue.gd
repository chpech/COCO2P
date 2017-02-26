#############################################################################
##  $Id: queue.gd,v 1.0 2008-12-06 10:05:05+01 zeka Exp zeka $
##
##  $Log: queue.gd,v $
##  Revision 1.0  2008-12-06 10:05:05+01  zeka
##  Initial revision
##
##
#############################################################################

Revision.queue_gd :=
  "@(#)$Id: queue.gd,v 1.0 2008-12-06 10:05:05+01 zeka Exp zeka $";

#############################################################################
##
##  queue.gd                  COCO package                      
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Declarations for queue datastructures
##
#############################################################################

DeclareGlobalFunction("FiFoNew");
DeclareGlobalFunction("FiFoAdd");
DeclareGlobalFunction("FiFoRemove");

