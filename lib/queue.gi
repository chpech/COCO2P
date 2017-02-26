############################################
##  $Id$
##
##  $Log$
##
############################################

Revision.queue_gi :=
  "@(#)$Id$";

#############################################################################
##
##  queue.gi                  COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of queue datastructures
##
#############################################################################


# this file implements a crude interface to fifo queues.
# A fifo-queue is a record:
#rec(
#    queue = [],
#    first = 1,
#    );

InstallGlobalFunction(FiFoNew,
function()
    local q;

    q:=rec();
    q.queue:=[];
    q.first:=1;
    return q;
end);


InstallGlobalFunction(FiFoAdd,
function(q, x)
    Add(q.queue, x);
end);


InstallGlobalFunction(FiFoRemove,
function(q)
    local x;

    if IsBound(q.queue[q.first]) then
        x:=q.queue[q.first];
        q.queue[q.first]:="empty";
        q.first:=q.first+1;
        if q.first>100 then
            q.queue:=q.queue{[q.first..Length(q.queue)]};
            q.first:=1;
        fi;
        return x;
    else
        return false;
    fi;
end);
