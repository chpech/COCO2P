#############################################################################
##
##  francy.gi                    COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of the jupyter interface using francy
##
#############################################################################


TestFrancyColor:=function()
    local canvas,graph,v1,v2,msg1,msg2,cbf,cb;
    
    canvas:=Canvas("test");
    graph := Graph(GraphType.DIRECTED);
    Add(canvas,graph);
    v1:=Shape(ShapeType.SQUARE);SetLayer(v1,1);
    v2:=Shape(ShapeType.WYE);SetLayer(v2,2);
    Add(graph,v1);
    Add(graph,v2);
    
    msg1:=FrancyMessage(FrancyMessageType.INFO, "message from v1");
    msg2:=FrancyMessage(FrancyMessageType.INFO, "message from v2");
    ###################
    cbf:=function(canvas,graph,vert)
        Add(canvas,msg1);
        return Draw(canvas);
    end;
    cb:=Callback(TriggerType.CLICK, cbf,[canvas,graph,v1]);
    Add(v1,cb);
    ###################
    cbf:=function(canvas,graph,vert)
        Remove(canvas,msg1);
        return Draw(canvas);
    end;
    cb:=Callback(TriggerType.RIGHT_CLICK, cbf,[canvas,graph,v1]);
    Add(v1,cb);
    ###################
    cbf:=function(canvas,graph,vert)
        Add(canvas,msg2);
        return Draw(canvas);
    end;
    cb:=Callback(TriggerType.CLICK, cbf,[canvas,graph,v2]);
    Add(v2,cb);
    ###################
    cbf:=function(canvas,graph,vert)
        Remove(canvas,msg2);
        return Draw(canvas);
    end;
    cb:=Callback(TriggerType.RIGHT_CLICK, cbf,[canvas,graph,v2]);
    Add(v2,cb);
    ###################
    ###################
    cbf:=function(canvas,graph,vert)
        Remove(canvas,msg2);
        return Draw(canvas);
    end;
    cb:=Callback(TriggerType.RIGHT_CLICK, cbf,[canvas,graph,v2]);
    Add(v2,cb);
    ###################
    
    
    return Draw(canvas);
    
end;



BindGlobal("CocoGraphDefaults", Objectify(NewType(GraphFamily, IsFrancyGraphDefaults and IsFrancyGraphDefaultsRep), 
                    rec(simulation:=true,
                        collapsed:=true )));

BindGlobal("CocoCanvasDefaults", Objectify(NewType(CanvasFamily, IsCanvasDefaults and IsCanvasDefaultsRep), rec(
  width          := 800,
  height         := 600,
  zoomToFit      := true,
  texTypesetting := false
                            )));

BindGlobal( "ClearGreen@",
function( gpos )
    local i;

    for i in gpos!.lastresult do
        SetColor(gpos!.vertices[i],"");
    od;
    
    gpos!.lastresult := [];
    return Draw(gpos!.canvas);
end );


GraphicCocoPosetFam := NewFamily("GraphicCocoPosetFam", IsGraphicCocoPoset);

DeclareRepresentation( "IsGraphicCocoPosetRep",
        IsComponentObjectRep,
        [ "canvas",      # francy canvas
          "graph",       # francy graph
          "poset",       # the coco poset
          "vertices",    # the francy vertices
          "nodes",       # the coco nodes
          "selected",    # selected vertices in graph
          "lastresult"]  # green vertices in graph
        );

InstallOtherMethod(Draw,
        "for graphic coco posets in GraphicCocoPosetRep",
        [IsGraphicCocoPoset and IsGraphicCocoPosetRep],
function(gpos)
    return Draw(gpos!.canvas);
end);


InstallMethod(GraphicCocoPoset,
        "for COCO-posets",
        [IsCocoPoset],
function(cocoposet)
    local   obj,nodes,node,shape,canvas, graph,  v,  vertices,  i,  elm,  j,  lev,levels,NewNode;


    NewNode:=function(poset,index,level)
        return Objectify(NewType(CocoNodesFam, IsCocoNode and IsCocoNodeRep),
                       rec( poset:=poset,
                            index:=index,
                            level:=level));
    end;
    
    
    canvas := Canvas( "COCO-poset" );
#    SetFilterObj(gposet, IsGraphicCocoPoset);
    graph := Graph(GraphType.DIRECTED,CocoGraphDefaults);
    SetSimulation(graph,false);
  #  SetDrag(graph,false);
  #  SetShowNeighbours(graph,false);
    
    Add(canvas, graph);
    
#    gposet!.lastresult:=[];
    
    vertices := [];nodes:=[];
    levels:=ListWithIdenticalEntries(Size(cocoposet),0);
    for i in [1..Size(cocoposet)] do
        for j in SuccessorsInCocoPoset(cocoposet,i) do
            if levels[j]<=levels[i] then
                levels[j]:=levels[i]+1;
            fi;
        od;
    od;
    
    for i in [1..Size(cocoposet)] do
        node:=NewNode(cocoposet,i,levels[i]);
        shape:=ShapeOfCocoNode(node);
        if shape="rectangle" then
            shape:=ShapeType.SQUARE;
        elif shape="circle" then
            shape:=ShapeType.CIRCLE;
        elif
          shape="diamond" then
            shape:=ShapeType.DIAMOND;
        else
            shape:=ShapeType.WYE;
        fi;
        v:=Shape(shape, String(i));
        SetLayer(v, -LevelOfCocoNode(node));
        Add( vertices, v);
        Add(graph,v);
        Add(nodes, node);
    od;
    for i in [1..Size(cocoposet)] do
        for j in SuccessorsInCocoPoset(cocoposet,i) do
            Add(graph, Link( vertices[i], vertices[j] ));
        od;
    od;
    
    obj:=rec(canvas:=canvas,
             graph:=graph,
             poset:=cocoposet,
             vertices:=vertices,
             nodes:=nodes,
             selected:=[],
             lastresult:=[]);
    return Objectify(NewType(GraphicCocoPosetFam, IsGraphicCocoPoset and IsGraphicCocoPosetRep), obj);
end);






InstallMethod(GraphicCocoPoset,
        "for sub color isomorphism posets",
        [IsCocoPoset and IsSubColorIsomorphismPoset],
function(cgrposet)
    local canvas,graph, vertices,nodes,node,shape,i,j,v,updater,setter,obj,m,cb, cbf,createInfoOnScreen,computeInfoOnScreen,clearInfoOnScreen,handlePopup,menu,mainMenu,clearwhite,reshapeAll,selectVertex,deselectAll,maxrank,updateAll;
    
    updater:=function(node,i)
        if node!.nodeInfo.values[i]<>"unknown" then
            return;
        fi;
        if node!.nodeInfo.testers[i](node) then
            node!.nodeInfo.values[i]:=node!.nodeInfo.toStr[i](node!.nodeInfo.getters[i](node));
        fi;
    end;
    
    setter:=function(node,i);
        if node!.nodeInfo.values[i]<>"unknown" then
            return;
        fi;
        node!.nodeInfo.values[i]:=node!.nodeInfo.toStr[i](node!.nodeInfo.getters[i](node));
    end;
    
    reshapeAll:=function(poset)
        local i,node,shp;
        
        for i in [1..Size(poset)] do
            node:=poset!.nodes[i];
            shp:=ShapeOfCocoNode(node);
            if shp="rectangle" then
                poset!.vertices[i]!.type:="square";
            elif shp="circle" then
                poset!.vertices[i]!.type:="circle";
            elif shp="diamond" then
                poset!.vertices[i]!.type:="diamond";
            else
                poset!.vertices[i]!.type:="wye";
            fi;
        od;
    end;
    
    updateAll:=function(poset)
        local i,j,node;
        for i in [1..Size(poset)] do
            node:=poset!.nodes[i];
            for j in [1..Length(node!.nodeInfo.names)] do 
                updater(node,j);
            od;
        od;
    end;
    
    clearwhite:=function(poset)
        local i;
        for i in poset!.lastresult do
            SetColor(poset!.vertices[i],"");
        od;
        poset!.lastresult:=[];
    end;
    
    deselectAll:=function(poset)
        local i,vrt;
        
        for i in [1..Size(poset)] do
            SetSelected(poset!.vertices[i],false);
        od;
    end;
    
    selectVertex:=function(poset,idx)
        local vrt;
        
        vrt:=poset!.vertices[idx];
        if Selected(vrt) then
            SetSelected(vrt,false);
        else
            SetSelected(vrt,true);
        fi;
        return Draw(poset!.canvas);
    end;
    
    handlePopup:=function(poset,nidx,idx)
        local node,vertex;
        node:=poset!.nodes[nidx];
        vertex:=poset!.vertices[nidx];
        
        setter(node,idx);
        if poset!.infoOnScreenIdx=nidx then
            SetValue(poset!.infoOnScreen[idx],node!.nodeInfo.values[idx]);
        fi;
        Remove(vertex,node!.menues[idx]);
        
        updateAll(poset);
        reshapeAll(poset);
        
        return createInfoOnScreen(poset,nidx);
    end;
           
    clearInfoOnScreen:=function(poset)
        local item;
        
        for item in poset!.infoOnScreen do 
            Remove(poset!.canvas, item);
        od;
        
        poset!.infoOnScreen:=[];
        poset!.infoOnScreenIdx:=0;
    end;    
    
    createInfoOnScreen:=function(poset,idx)
        local node,message,i;
        
        clearInfoOnScreen(poset);
        
     #   Add(canvas, FrancyMessage(FrancyMessageType.ERROR, String(canvas!.messages)));
        node:=poset!.nodes[idx];
        
        for i in [1..Length(node!.nodeInfo.names)] do
            updater(node,i);
            message :=FrancyMessage(FrancyMessageType.INFO, String(node!.nodeInfo.names[i],-node!.nodeInfo.maxlength), node!.nodeInfo.values[i]);
            Add(poset!.canvas, message);
            Add(poset!.infoOnScreen,message);
#            if node!.nodeInfo.values[i]="unknown" then
#                cb:=Callback(TriggerType.DOUBLE_CLICK, computeInfoOnScreen, [canvas,node,message,i]);
#                Add(message,cb);
#            fi;
        od;
        poset!.infoOnScreenIdx:=idx;
        
        return Draw(poset!.canvas);
        
    end;

    cgrposet!.canvas:= Canvas ("SubColorIsomorphismPoset", CocoCanvasDefaults);
    cgrposet!.infoOnScreen:=[];
    cgrposet!.infoOnScreenIdx:=0;
    
    graph:=Graph(GraphType.UNDIRECTED, CocoGraphDefaults);
    Add(cgrposet!.canvas,graph);
    
    cgrposet!.vertices:=[];
    cgrposet!.nodes:=[];
    cgrposet!.lastresult:=[];
    
                        
    maxrank:=Maximum(List(ElementsOfCocoPoset(cgrposet),RankOfColorGraph));
    
    for i in [1..Size(cgrposet)] do
        node:=NewCocoNode(cgrposet,i);
        shape:=ShapeOfCocoNode(node);
        if shape="rectangle" then
            shape:=ShapeType.SQUARE;
        elif shape="circle" then
            shape:=ShapeType.CIRCLE;
        elif
          shape="diamond" then
            shape:=ShapeType.DIAMOND;
        else
            shape:=ShapeType.WYE;
        fi;
        v:=Shape(shape, String(i));
        Add(cgrposet!.nodes,node);
        Add(cgrposet!.vertices,v);
        node!.menues:=[];
        
        for j in [1..Length(node!.nodeInfo.names)] do
            updater(node,j);
            
            if node!.nodeInfo.values[j]="unknown" then
                cb := Callback(handlePopup, [cgrposet,i,j]);
                node!.menues[j]:=Menu(node!.nodeInfo.names[j],cb);
                Add(v, node!.menues[j]);
            fi;
        od;
        cb:=Callback(TriggerType.CLICK, 
                    createInfoOnScreen,[cgrposet,i]);
        Add(v,cb);
        cb:=Callback(TriggerType.CLICK,
                    selectVertex,[cgrposet,i]);
        Add(v,cb);
        SetSelected(v,false);
        
        SetLayer(v, maxrank-LevelOfCocoNode(node));
        Add(graph,v);
    od;
    
    for i in [1..Size(cgrposet)] do
        for j in SuccessorsInCocoPoset(cgrposet,i) do
            Add(graph, Link( cgrposet!.vertices[j], cgrposet!.vertices[i] ));
        od;
    od;

    
    mainMenu:=Menu("Properties");
    
    ################################
    cbf:=function(poset) # Primitive
        local Vs,i;
        clearwhite(poset);
        
        Vs:=Filtered([1..Size(poset)], i->IsPrimitiveColorGraph(poset!.elements[i]));
        for i in Vs do
            SetColor(poset!.vertices[i],"white");
            Add(poset!.lastresult,i);
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("Primitive",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # Symmetric
        local Vs,i;
        clearwhite(poset);
        
        Vs:=Filtered([1..Size(poset)], i->IsSymmetricColorGraph(poset!.elements[i]));
        for i in Vs do
            SetColor(poset!.vertices[i],"white");
            Add(poset!.lastresult,i);
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("Symmetric",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # Commutative
        local Vs,i;
        clearwhite(poset);
        
        Vs:=Filtered([1..Size(poset)], i->IsCommutativeTensor(StructureConstantsOfColorGraph(poset!.elements[i])));
        for i in Vs do
            SetColor(poset!.vertices[i],"white");
            Add(poset!.lastresult,i);
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("Commutative",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # non-Schurian
        local Vs,i;
        clearwhite(poset);
        
        Vs:=Filtered([1..Size(poset)], i->not IsSchurian(poset!.elements[i]));
        for i in Vs do
            SetColor(poset!.vertices[i],"white");
            Add(poset!.lastresult,i);
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("non-Schurian",cb);
    Add(mainMenu,menu);
    ################################
    Add(cgrposet!.canvas,mainMenu);
##############################################    
    mainMenu:=Menu("Symmetries");
    
    cbf:=function(poset) # compute Aut
        local Vs,i,j,node,idx;
        
        Vs:=Filtered([1..Size(poset)], i->Selected(poset!.vertices[i]));
        
        for i in Vs do
            node:=poset!.nodes[i];
            idx:=Position(node!.nodeInfo.names,"Aut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for j in [1..Length(node!.nodeInfo.names)] do
                updater(node,j);
            od;
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            return createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        else
            return Draw(poset!.canvas);
        fi;
        
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("compute Aut",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # compute cAut/Aut
        local Vs,i,j,node,idx;
        
        Vs:=Filtered([1..Size(poset)], i->Selected(poset!.vertices[i]));
        
        for i in Vs do
            node:=poset!.nodes[i];
            idx:=Position(node!.nodeInfo.names,"cAut/Aut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for j in [1..Length(node!.nodeInfo.names)] do
                updater(node,j);
            od;
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            return createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        else
            return Draw(poset!.canvas);
        fi;
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("compute cAut/Aut",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # compute aAut
        local Vs,i,j,node,idx;
        
        Vs:=Filtered([1..Size(poset)], i->Selected(poset!.vertices[i]));
        
        for i in Vs do
            node:=poset!.nodes[i];
            idx:=Position(node!.nodeInfo.names,"aAut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for j in [1..Length(node!.nodeInfo.names)] do
                updater(node,j);
            od;
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            return createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        else
            return Draw(poset!.canvas);
        fi;
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("compute aAut",cb);
    Add(mainMenu,menu);
    ################################
    Add(cgrposet!.canvas,mainMenu);
##############################################    
    mainMenu:=Menu("Selection");
    
    
    cbf:= function(poset) # select white
        local i;
        
        deselectAll(poset);
        for i in poset!.lastresult do
            SetSelected( poset!.vertices[i] ,true );
        od;
        clearwhite( poset );
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("Select White",cb);
    Add(mainMenu,menu);
    ################################
    cbf:= function(poset) # invert selection
        local i,vrt;
        for i in [1..Size(poset)] do
            vrt:=poset!.vertices[i];
            if Selected(vrt) then
                SetSelected(vrt,false);
            else
                SetSelected(vrt,true);
            fi;
        od;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("Invert Selection",cb);
    Add(mainMenu,menu);
    ################################
    cbf:= function(poset) # clear selection
        local i;
        for i in [1..Size(poset)] do
            SetSelected(poset!.vertices[i],false);
        od;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("Clear Selection",cb);
    Add(mainMenu,menu);
    ################################
    cbf:= function(poset) # report
        local i;
        
        return ("test\n");
        
        # for i in [1..Size(poset)] do
        #     SetSelected(poset!.vertices[i],false);
        # od;
#        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[cgrposet]);
    menu:=Menu("Report",cb);
    Add(mainMenu,menu);
    ################################
 
    
    Add(cgrposet!.canvas,mainMenu);
    
    
    
    return Draw(cgrposet!.canvas);
    
    obj:=rec(canvas:=canvas,
             graph:=graph,
             poset:=cgrposet,
             vertices:=vertices,
             nodes:=nodes,
             selected:=[],
             lastresult:=[]);
    return Objectify(NewType(GraphicCocoPosetFam, IsGraphicCocoPoset and IsGraphicCocoPosetRep), obj);
end);

InstallMethod(GraphicCocoPoset,
        "for posets of fusion orbits",
        [IsPosetOfFusionOrbits and IsPosetOfFusionOrbitsRep],
function(forbposet)
    local updater, setter, reshapeAll, clearwhite,deselectAll,selectVertex,handlePopup,clearInfoOnScreen,createInfoOnScreen,updateAll,graph,maxrank,lcls,i,node,shape,v,j,cb,mainMenu,cbf,menu;

    
    updater:=function(node,i)
        if node!.nodeInfo.values[i]<>"unknown" then
            return;
        fi;
        if node!.nodeInfo.testers[i](node) then
            node!.nodeInfo.values[i]:=node!.nodeInfo.toStr[i](node!.nodeInfo.getters[i](node));
        fi;
    end;
    
    setter:=function(node,i);
        if node!.nodeInfo.values[i]<>"unknown" then
            return;
        fi;
        node!.nodeInfo.values[i]:=node!.nodeInfo.toStr[i](node!.nodeInfo.getters[i](node));
    end;
    
    reshapeAll:=function(poset)
        local i,node,shp;
        
        for i in [1..Size(poset)] do
            node:=poset!.nodes[i];
            shp:=ShapeOfCocoNode(node);
            if shp="rectangle" then
                poset!.vertices[i]!.type:="square";
            elif shp="circle" then
                poset!.vertices[i]!.type:="circle";
            elif shp="diamond" then
                poset!.vertices[i]!.type:="diamond";
            else
                poset!.vertices[i]!.type:="wye";
            fi;
        od;
    end;
    
    updateAll:=function(poset)
        local i,j,node;
        for i in [1..Size(poset)] do
            node:=poset!.nodes[i];
            for j in [1..Length(node!.nodeInfo.names)] do 
                updater(node,j);
            od;
        od;
    end;
    
            
    clearwhite:=function(poset)
        local i;
        for i in poset!.lastresult do
            SetColor(poset!.vertices[i],"");
        od;
        poset!.lastresult:=[];
    end;
    
    deselectAll:=function(poset)
        local i,vrt;
        
        for i in [1..Size(poset)] do
            SetSelected(poset!.vertices[i],false);
        od;
    end;
    
    selectVertex:=function(poset,idx)
        local vrt;
        
        vrt:=poset!.vertices[idx];
        if Selected(vrt) then
            SetSelected(vrt,false);
        else
            SetSelected(vrt,true);
        fi;
        return Draw(poset!.canvas);
    end;
    
    handlePopup:=function(poset,nidx,idx)
        local node,vertex;
        node:=poset!.nodes[nidx];
        vertex:=poset!.vertices[nidx];
        
        setter(node,idx);
        Remove(vertex,node!.menues[idx]);
        if poset!.infoOnScreenIdx=nidx then
            SetValue(poset!.infoOnScreen[idx],node!.nodeInfo.values[idx]);
        fi;
        updateAll(poset);
        reshapeAll(poset);
        
        return createInfoOnScreen(poset,nidx);
    end;
           
    clearInfoOnScreen:=function(poset)
        local item;
        
        for item in poset!.infoOnScreen do 
            Remove(poset!.canvas, item);
        od;
        
        poset!.infoOnScreen:=[];
        poset!.infoOnScreenIdx:=0;
    end;    
    
    createInfoOnScreen:=function(poset,idx)
        local node,message,i;
        
        clearInfoOnScreen(poset);
        
     #   Add(canvas, FrancyMessage(FrancyMessageType.ERROR, String(canvas!.messages)));
        node:=poset!.nodes[idx];
        
        for i in [1..Length(node!.nodeInfo.names)] do
            updater(node,i);
            message :=FrancyMessage(FrancyMessageType.INFO, String(node!.nodeInfo.names[i],-node!.nodeInfo.maxlength), node!.nodeInfo.values[i]);
            Add(poset!.canvas, message);
            Add(poset!.infoOnScreen,message);
#            if node!.nodeInfo.values[i]="unknown" then
#                cb:=Callback(TriggerType.DOUBLE_CLICK, computeInfoOnScreen, [canvas,node,message,i]);
#                Add(message,cb);
#            fi;
        od;
        poset!.infoOnScreenIdx:=idx;
        
        return Draw(poset!.canvas);
        
    end;
    
    forbposet!.canvas:=Canvas("PosetOfFusionOrbits", CocoCanvasDefaults);
    forbposet!.infoOnScreen:=[];
    forbposet!.infoOnScreenIdx:=0;
    
    graph:=Graph(GraphType.UNDIRECTED, CocoGraphDefaults);
    Add(forbposet!.canvas,graph);
    
    forbposet!.vertices:=[];
    forbposet!.nodes:=[];
    forbposet!.lastresult:=[];
    
    maxrank:=Maximum(List(forbposet!.colorGraphs,RankOfColorGraph));
    
    
    lcls:=List([1..Size(forbposet)],x->Union([x],forbposet!.algTwins[x]));
    
    
    for i in [1..Size(forbposet)] do
        node:=NewCocoNode(forbposet,i);
        shape:=ShapeOfCocoNode(node);
        if shape="rectangle" then
            shape:=ShapeType.SQUARE;
        elif shape="circle" then
            shape:=ShapeType.CIRCLE;
        elif
          shape="diamond" then
            shape:=ShapeType.DIAMOND;
        else
            shape:=ShapeType.WYE;
        fi;
        v:=Shape(shape, String(i));
        Add(forbposet!.nodes,node);
        Add(forbposet!.vertices,v);
        node!.menues:=[];
        for j in [1..Length(node!.nodeInfo.names)] do
            updater(node,j);
            
            if node!.nodeInfo.values[j]="unknown" then
                cb := Callback(handlePopup, [forbposet,i,j]);
                node!.menues[j]:=Menu(node!.nodeInfo.names[j],cb);
                Add(v, node!.menues[j]);
            fi;
        od;
        cb:=Callback(TriggerType.CLICK, 
                    createInfoOnScreen,[forbposet,i]);
        Add(v,cb);
        cb:=Callback(TriggerType.CLICK,
                    selectVertex,[forbposet,i]);
        Add(v,cb);
        SetSelected(v,false);
        
        SetLayer(v, maxrank-LevelOfCocoNode(node));
        Add(graph,v);
    od;


    for i in [1..Size(forbposet)] do
      for j in SuccessorsInCocoPoset(forbposet,i) do
          Add(graph, Link( forbposet!.vertices[j], forbposet!.vertices[i] ));
      od;
    od;
    
        mainMenu:=Menu("Properties");
    
    ################################
    cbf:=function(poset) # Primitive
        local Vs,i;
        clearwhite(poset);
        
        Vs:=Filtered([1..Size(poset)], i->IsPrimitiveColorGraph(poset!.colorGraphs[i]));
        for i in Vs do
            SetColor(poset!.vertices[i],"white");
            Add(poset!.lastresult,i);
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("Primitive",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # Symmetric
        local Vs,i;
        clearwhite(poset);
        
        Vs:=Filtered([1..Size(poset)], i->IsSymmetricColorGraph(poset!.colorGraphs[i]));
        for i in Vs do
            SetColor(poset!.vertices[i],"white");
            Add(poset!.lastresult,i);
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("Symmetric",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # Commutative
        local Vs,i;
        clearwhite(poset);
        
        Vs:=Filtered([1..Size(poset)], i->IsCommutativeTensor(StructureConstantsOfColorGraph(poset!.colorGraphs[i])));
        for i in Vs do
            SetColor(poset!.vertices[i],"white");
            Add(poset!.lastresult,i);
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("Commutative",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # non-Schurian
        local Vs,i;
        clearwhite(poset);
        
        Vs:=Filtered([1..Size(poset)], i->not IsSchurian(poset!.colorGraphs[i]));
        for i in Vs do
            SetColor(poset!.vertices[i],"white");
            Add(poset!.lastresult,i);
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("non-Schurian",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # algebraic
        local Vs,i;
        clearwhite(poset);
        
        for i in poset!.algebraicFusions do
            SetColor(poset!.vertices[i],"white");
            Add(poset!.lastresult,i);
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("algebraic",cb);
    Add(mainMenu,menu);
    ################################
    Add(forbposet!.canvas,mainMenu);
##############################################    
    mainMenu:=Menu("Symmetries");
    
    cbf:=function(poset) # compute Aut
        local Vs,i,j,node,idx;
        
        Vs:=Filtered([1..Size(poset)], i->Selected(poset!.vertices[i]));
        
        for i in Vs do
            node:=poset!.nodes[i];
            idx:=Position(node!.nodeInfo.names,"Aut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for j in [1..Length(node!.nodeInfo.names)] do
                updater(node,j);
            od;
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        fi;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("compute Aut",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # compute cAut/Aut
        local Vs,i,j,node,idx;
        
        Vs:=Filtered([1..Size(poset)], i->Selected(poset!.vertices[i]));
        
        for i in Vs do
            node:=poset!.nodes[i];
            idx:=Position(node!.nodeInfo.names,"cAut/Aut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for j in [1..Length(node!.nodeInfo.names)] do
                updater(node,j);
            od;
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            return createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        else
            return Draw(poset!.canvas);
        fi;
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("compute cAut/Aut",cb);
    Add(mainMenu,menu);
    ################################
    cbf:=function(poset) # compute aAut
        local Vs,i,j,node,idx;
        
        Vs:=Filtered([1..Size(poset)], i->Selected(poset!.vertices[i]));
        
        for i in Vs do
            node:=poset!.nodes[i];
            idx:=Position(node!.nodeInfo.names,"aAut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for j in [1..Length(node!.nodeInfo.names)] do
                updater(node,j);
            od;
        od;
        updateAll(poset);
        reshapeAll(poset);
        if poset!.infoOnScreenIdx<>0 then
            return createInfoOnScreen(poset,poset!.infoOnScreenIdx);
        else
            return Draw(poset!.canvas);
        fi;
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("compute aAut",cb);
    Add(mainMenu,menu);
    ################################
    Add(forbposet!.canvas,mainMenu);
##############################################    
    mainMenu:=Menu("Selection");
    
    
    cbf:= function(poset) # select white
        local i;
        
        deselectAll(poset);
        for i in poset!.lastresult do
            SetSelected( poset!.vertices[i] ,true );
        od;
        clearwhite( poset );
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("Select White",cb);
    Add(mainMenu,menu);
    ################################
    cbf:= function(poset) # invert selection
        local i,vrt;
        for i in [1..Size(poset)] do
            vrt:=poset!.vertices[i];
            if Selected(vrt) then
                SetSelected(vrt,false);
            else
                SetSelected(vrt,true);
            fi;
        od;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("Invert Selection",cb);
    Add(mainMenu,menu);
    ################################
    cbf:= function(poset) # clear selection
        local i;
        for i in [1..Size(poset)] do
            SetSelected(poset!.vertices[i],false);
        od;
        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("Clear Selection",cb);
    Add(mainMenu,menu);
    ################################
    cbf:= function(poset) # report
        local i;
        
        return ("test\n");
        
        # for i in [1..Size(poset)] do
        #     SetSelected(poset!.vertices[i],false);
        # od;
#        return Draw(poset!.canvas);
    end;
    cb:=Callback(cbf,[forbposet]);
    menu:=Menu("Report",cb);
    Add(mainMenu,menu);
    ################################
 
    
    Add(forbposet!.canvas,mainMenu);
    
    return Draw(forbposet!.canvas);
end);


