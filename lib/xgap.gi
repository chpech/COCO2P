#############################################################################
##
##  xgap.gi                      COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation of the xgap interface
##
#############################################################################


DeclareRepresentation( "IsGraphicCocoPosetRep",
  IsComponentObjectRep and IsAttributeStoringRep and IsGraphicSheet and
  IsGraphicSheetRep and IsGraphicGraphRep and IsGraphicPosetRep,
# we inherit those components from the sheet:
  [ "name", "width", "height", "gapMenu", "callbackName", "callbackFunc",
    "menus", "objects", "free",
# and the following from being a poset:
    "levels",           # list of levels, stores current total ordering
    "levelparams",      # list of level parameters
    "selectedvertices", # list of selected vertices
    "menutypes",        # one entry per menu which contains list of types
    "menuenabled",      # one entry per menu which contains list of flags
    "rightclickfunction",    # the current function which is called when
                             # user clicks right button
    "color",            # some color infos for the case of different models
    "levelboxes",       # little graphic boxes for the user to handle levels
    "showlevels",       # flag, if levelboxes are shown
# now follow our own components:
    "lastresult" ],      # list of vertices which are "green"
    IsGraphicSheet );


BindGlobal( "ClearGreen@",
function( gpos )
local sel, v;

    sel := Selected(gpos);
    for v in gpos!.lastresult do
        if IsAlive(v) then
            if PositionSet(sel,v) = fail then
                Recolor(gpos,v,gpos!.color.unselected);
            else
                Recolor(gpos,v,gpos!.color.selected);
            fi;
        fi;
    od;
    gpos!.lastresult := [];
end );

BindGlobal( "ReshapeAll@",
  function( gpos )
  local lev, class, vert, sel;
    sel := Selected( gpos );
    for lev in Levels( gpos ) do
      for class in Classes( gpos, lev ) do
        for vert in Vertices( gpos, lev, class ) do
            Reshape( gpos, vert );
        od;
      od;
    od;
end );



InstallMethod(ChooseShape,
        "for graphic coco posets",
        [IsGraphicCocoPoset and IsGraphicPosetRep, IsCocoNode],
function(poset,data)
    return ShapeOfCocoNode(data);
end);

# InstallMethod(
# 	ChooseShape,
# 	"for graphic coco posets of color graphs",
# 	[IsGraphicCocoPoset and IsGraphicPosetRep,IsCocoNode and IsColorGraphNodeRep],
# function( cgrposet, data )
#     local cgr;
#     cgr := data!.cgr;
#     if RankOfColorGraph(cgr)=2 then
#         return "circle";
#     fi;
#     if RankOfColorGraph(cgr)=3 and not IsPrimitiveColorGraph(cgr) then
#         return "circle";
#     fi;
    
#     if HasIsSchurian( cgr ) then
#         if IsSchurian( cgr ) then
#             return "circle";
#         else
#             return "diamond";
#         fi;
#     else
#         return "rectangle";
#     fi;
# end );


InstallMethod(ChooseLevel,
	"for graphic coco posets of color graphs",
	[IsGraphicCocoPoset and IsGraphicPosetRep, IsCocoNode],
function( cocoposet, data )
    return LevelOfCocoNode(data);
end );

InstallMethod(
	CompareLevels,
	"for graphic coco posets",
	[ IsGraphicCocoPoset and IsGraphicPosetRep, IsInt, IsInt ],
function( poset, a, b )
    if a < b then
	return 1;
    elif a > b then
	return -1;
    else
	return 0;
    fi;
end);

InstallMethod(GraphicCocoPoset,
        "for COCO-posets",
        [IsCocoPoset],
function(cocoposet)
    local   gposet,  vertices,  i,  elm,  j,  lev,levels,NewNode;


    NewNode:=function(poset,index,level)
        return Objectify(NewType(CocoNodesFam, IsCocoNode and IsCocoNodeRep),
                       rec( poset:=poset,
                            index:=index,
                            level:=level));
    end;


    gposet := GraphicPoset( "COCO-poset", 800, 600 );

    SetFilterObj( gposet, IsGraphicCocoPoset and IsGraphicCocoPosetRep );
    gposet!.lastresult:=[];

    vertices := [];
    levels:=ListWithIdenticalEntries(Size(cocoposet),0);
    for i in [1..Size(cocoposet)] do
        for j in SuccessorsInCocoPoset(cocoposet,i) do
            if levels[j]<=levels[i] then
                levels[j]:=levels[i]+1;
            fi;
        od;
    od;
    for i in [1..Maximum(levels)] do
        CreateLevel(gposet, i);
    od;

    for i in [1..Size(cocoposet)] do
	Add( vertices, Vertex( gposet, NewNode(cocoposet,i,levels[i]),
			rec( label := String( i ))));
    od;
    for i in [1..Size(cocoposet)] do
      for j in SuccessorsInCocoPoset(cocoposet,i) do
	Edge( gposet, vertices[i], vertices[j] );
      od;
    od;
    return gposet;
end);







InstallMethod(GraphicCocoPoset,
        "for sub color isomorphism posets",
        [IsCocoPoset and IsSubColorIsomorphismPoset],
function(cgrposet)
    local gposet,levels, vertices, classes,lcls,i,j,cgr,funcclose,funcall,updater,setter,node;


    gposet := GraphicPoset( "SubColorIsomorphismPoset", 800, 600 );
    gposet!.infobox:=false;


    SetFilterObj( gposet, IsGraphicCocoPoset );
    gposet!.lastresult:=[];
    levels:=Set(ElementsOfCocoPoset(cgrposet), RankOfColorGraph);

    for i in levels do
        CreateLevel( gposet, i );
    od;

    vertices:=[];

    for i in [1..Size(cgrposet)] do
        cgr:=ElementsOfCocoPoset(cgrposet)[i];
        
        node:=NewCocoNode(ElementsOfCocoPoset(cgrposet)[i]);
        node!.index:=i;
        RegisterInfoCocoNode(node, rec(name:="Number:",value:=String(i)));
        RegisterStandardInfo@(node);

        Add( vertices, Vertex( gposet, node,
                rec( label := String( i )
                              ) ) );
    od;

    for i in [1..Size(cgrposet)] do
      for j in SuccessorsInCocoPoset(cgrposet,i) do
	Edge( gposet, vertices[i], vertices[j] );
      od;
    od;

    Menu( gposet, "Properties",
          [
           "Primitive",
           "Symmetric",
           "Commutative",
           "non-Schurian"
           ],
          [
           "forany",
           "forany",
           "forany",
           "forany"
           ],
          [
           # Primitive
           function(gpos, menu, entry)
        local V,Vs;
        Vs:=WhichVertices(gpos,[], function(data,vertex)
            return IsPrimitiveColorGraph(vertex!.cgr);
        end);
        ClearGreen@( gpos );

        for V in Vs do
            Recolor( gpos, V, COLORS.green );
            Add(gpos!.lastresult,V);
        od;
    end,
        # Symmetric
      function(gpos, menu, entry)
        local V,Vs;
        Vs:=WhichVertices(gpos,[], function(data,vertex)
            return IsSymmetricColorGraph(vertex!.cgr);
        end);
        ClearGreen@( gpos );

        for V in Vs do
            Recolor( gpos, V, COLORS.green );
            Add(gpos!.lastresult,V);
        od;
    end,
        # commutative
      function(gpos, menu, entry)
        local V,Vs;
        Vs:=WhichVertices(gpos,[], function(data,vertex)
            return IsCommutativeTensor(StructureConstantsOfColorGraph(vertex!.cgr));
        end);
        ClearGreen@( gpos );

        for V in Vs do
            Recolor( gpos, V, COLORS.green );
            Add(gpos!.lastresult,V);
        od;
    end,
        # non-Schurian
      function(gpos, menu, entry)
        local V,Vs;
        Vs:=WhichVertices(gpos,[], function(data,vertex)
            return not IsSchurian(vertex!.cgr);
        end);
        ClearGreen@( gpos );
        ReshapeAll@(gpos);

        for V in Vs do
            Recolor( gpos, V, COLORS.green );
            Add(gpos!.lastresult,V);
        od;
    end
      ]);
    Menu( gposet, "Symmetries",
          [
           "compute Aut",
           "compute cAut/Aut",
           "compute aAut"
           ],
          [
           "forsubset",
           "forsubset",
           "forsubset"
           ],
          [
           # compute Aut
           function(gpos,menu,entry)
        local sel,v,node,idx,i;
        
        sel:=Selected(gpos);
        for v in sel do
            node:=v!.data;
            idx:=Position(node!.nodeInfo.names,"Aut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for i in [1..Length(node!.nodeInfo.names)] do
                updater(node,i);
            od;
            ReshapeAll@(gpos);
        od;
    end,
      # compute cAut/Aut
      function(gpos,menu,entry)
        local sel,v,node,idx,i;
        
        sel:=Selected(gpos);
        for v in sel do
            node:=v!.data;
            idx:=Position(node!.nodeInfo.names,"cAut/Aut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for i in [1..Length(node!.nodeInfo.names)] do
                updater(node,i);
            od;
        od;
    end,
      # compute aAut
      function(gpos,menu,entry)
        local sel,v,node,idx,i;
        
        sel:=Selected(gpos);
        for v in sel do
            node:=v!.data;
            idx:=Position(node!.nodeInfo.names,"aAut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for i in [1..Length(node!.nodeInfo.names)] do
                updater(node,i);
            od;
        od;
    end
      ]);
    
        Menu( gposet, "Selection",
          [
           "Select Green",
           "Invert Selection",,
           "Report..."
           ],
          [
           "forany",
           "forany",,
           "forsubset"
           ],
          [
        # select green
           function(gpos, menu, entry)
        local sel,V;
        sel:=gpos!.lastresult;
        DeselectAll(gpos);
        ClearGreen@( gpos );
        
        for V in sel do
            Select( gpos, V );
        od;
    end,
      # invert selection
      function(gpos,menu,entry)
        local sel,lev,class,vert;
        sel:=Selected(gpos);
        DeselectAll(gpos);
        for lev in Levels( gpos ) do
            for class in Classes( gpos, lev ) do
                for vert in Vertices( gpos, lev, class ) do
                    if not( vert in sel ) then
                        Select(gpos,vert);
                    fi;
                od;
            od;
        od;
    end,,
      # report
      function(gpos,menu,entry)
        local sel,di,res,v,node,ninf,i,pos,strictupperbounds,maxin,maxlength,indices,index,cgr;
        
        sel:=Selected(gpos);
        SortBy(sel, v->IndexOfCocoNode(v!.data));
        indices:=List(sel, x->IndexOfCocoNode(x!.data));
        
        di := Dialog("Filename","Log File?");
        res:= Query(di,"coco2p.info");
        PrintTo(res,"COCO2P - Informations about a SubColorIsomorphismPoset\n",
                "----------------------------------------------------\n");
        
        if res <> false then
            for v in sel do
                node:=v!.data;
                ninf:=node!.nodeInfo;
                maxlength:=Maximum(ninf.maxlength, 20);
                index:=IndexOfCocoNode(node);
                AppendTo(res, NodeInfoString(node));
                pos:=node!.poset;
                strictupperbounds:=Difference(FilterInCocoPoset(pos,index),[index]);
                strictupperbounds:=Intersection(strictupperbounds,indices);
                maxin:=[];
                if strictupperbounds<>[] then
                    maxin:=MinimalElementsInCocoPoset(pos,strictupperbounds);
                fi;
                AppendTo(res, String("Maximal Merging in: ",-maxlength), maxin,"\n");
                AppendTo(res,"\n");
            od;
        fi;
        end]);

  # close text selector
    funcclose := function( sel, bt )
        gposet!.infobox := false;
        Close(sel);
        return true;
    end;

    funcall := function( sel, bt )
        local i;
        for i  in [ 1 .. Length(sel!.labels) ]  do
            sel!.selected := i;
            sel!.textFuncs[i]( sel, sel!.labels[i] );
        od;
        Enable( sel, "all", false );
        return true;
    end;

    updater:=function(node,i)
        local val;
        
        if node!.nodeInfo.values[i]<>"unknown" then
            return;
        fi;
        if node!.nodeInfo.testers[i](node) then
            val:=node!.nodeInfo.getters[i](node);
            if val<>fail then
                node!.nodeInfo.values[i]:=node!.nodeInfo.toStr[i](val);
            fi;
        fi;
    end;
    
    setter:=function(node,i)
        local val;
        
        if node!.nodeInfo.values[i]<>"unknown" then
            return;
        fi;
        val:=node!.nodeInfo.getters[i](node);
        if val<>fail then
            node!.nodeInfo.values[i]:=node!.nodeInfo.toStr[i](val);
        fi;
    end;
    
        
    InstallPopup( gposet,
    function( sheet, vert, x, y )
	local id, texts,node;

        if sheet!.infobox <> false then
            Close(sheet!.infobox);
            sheet!.infobox := false;
        fi;

        if vert=fail then
            PopupFromMenu(sheet!.menus[3]);
            return;
        fi;
        node:=vert!.data;

        texts:=[];
        for i in [1..Length(node!.nodeInfo.names)] do
            updater(node,i);
            Add(texts, Concatenation(String(node!.nodeInfo.names[i],-node!.nodeInfo.maxlength), node!.nodeInfo.values[i]));
            Add(texts, function(x,y)
                   local ret,i;

                   ret:=node!.nodeInfo.getters[x!.selected](node);
                   if ret <> fail then
                       node!.nodeInfo.values[x!.selected]:=node!.nodeInfo.toStr[x!.selected](ret);
                   fi;

                #Relabel(x,x!.selected,Concatenation(node!.nodeInfo.names[x!.selected],node!.nodeInfo.values[x!.selected]));
                for i in [1..Length(node!.nodeInfo.names)] do
                    updater(node,i);
                    Relabel(x,i,Concatenation(String(node!.nodeInfo.names[i],-node!.nodeInfo.maxlength),node!.nodeInfo.values[i]));
                od;

                Reshape( gposet, vert);
                return ret;
            end);
        od;

        sheet!.infobox := TextSelector("",
        texts,
	[ "all", funcall, "close", funcclose ] );
    end);
    return gposet;
end);


InstallMethod(GraphicCocoPoset,
        "for posets of fusion orbits",
        [IsPosetOfFusionOrbits and IsPosetOfFusionOrbitsRep],
function(forbposet)
    local gposet,levels, vertices, classes,lcls,i,j,cgr,funcclose,funcall,updater,setter,node;


    gposet := GraphicPoset( "PosetOfFusionOrbits", 800, 600 );
    gposet!.infobox:=false;
    gposet!.lastresult:=[];

    SetFilterObj( gposet, IsGraphicCocoPoset );

    levels:=Set(forbposet!.colorGraphs, RankOfColorGraph);
    vertices:=[];
    classes:=[];

    lcls:=List([1..Size(forbposet)],x->Union([x],forbposet!.algTwins[x]));

    for i in levels do
        CreateLevel( gposet, i );
        for j in lcls do
            CreateClass( gposet, i, j );
        od;
    od;

    for i in [1..Size(forbposet)] do
        cgr:=forbposet!.colorGraphs[i];
        
        node:=NewCocoNode(forbposet!.colorGraphs[i]);
        node!.index:=i;
        node!.poset:=pos;

        RegisterInfoCocoNode(node, rec(name:="Number:", value:=String(i)));
        RegisterStandardInfo@(node);
        RegisterInfoCocoNode(node, rec(name:="algebraic:", value:=String(node!.index in node!.poset!.algebraicFusions)));

        Add( vertices, Vertex( gposet, node,
                rec(
                     label := String( i ),
                              levelparam := Rank(cgr),
                              classparam:=lcls[i] ) ) );
    od;

    for i in [1..Size(forbposet)] do
      for j in SuccessorsInCocoPoset(forbposet,i) do
	Edge( gposet, vertices[i], vertices[j] );
      od;
    od;

    Menu( gposet, "Properties",
          [
           "Primitive",
           "Symmetric",
           "Commutative",
           "non-Schurian",
           "algebraic"
           ],
          [
           "forany",
           "forany",
           "forany",
           "forany",
           "forany"
           ],
          [
           # Primitive
           function(gpos, menu, entry)
        local V,Vs;
        Vs:=WhichVertices(gpos,[], function(data,vertex)
            return IsPrimitiveColorGraph(vertex!.cgr);
        end);
        ClearGreen@( gpos );

        for V in Vs do
            Recolor( gpos, V, COLORS.green );
            Add(gpos!.lastresult,V);
        od;
    end,
      # Symmetric
      function(gpos, menu, entry)
        local V,Vs;
        Vs:=WhichVertices(gpos,[], function(data,vertex)
            return IsSymmetricColorGraph(vertex!.cgr);
        end);
        ClearGreen@( gpos );

        for V in Vs do
            Recolor( gpos, V, COLORS.green );
            Add(gpos!.lastresult,V);
        od;
    end,
      # commutative
      function(gpos, menu, entry)
        local V,Vs;
        Vs:=WhichVertices(gpos,[], function(data,vertex)
            return IsCommutativeTensor(StructureConstantsOfColorGraph(vertex!.cgr));
        end);
        ClearGreen@( gpos );

        for V in Vs do
            Recolor( gpos, V, COLORS.green );
            Add(gpos!.lastresult,V);
        od;
    end,
      # non-Schurian
      function(gpos, menu, entry)
        local V,Vs;
        Vs:=WhichVertices(gpos,[], function(data,vertex)
            return not IsSchurian(vertex!.cgr);
        end);
        ClearGreen@( gpos );
        ReshapeAll@(gpos);
        
        for V in Vs do
            Recolor( gpos, V, COLORS.green );
            Add(gpos!.lastresult,V);
        od;
    end,
      # algebraic
      function(gpos, menu, entry)
        local V,Vs;
        Vs:=WhichVertices(gpos,[], function(data,vertex)
            return vertex!.index in vertex!.poset!.algebraicFusions;
        end);
        ClearGreen@( gpos );

        for V in Vs do
            Recolor( gpos, V, COLORS.green );
            Add(gpos!.lastresult,V);
        od;
    end]);

    Menu( gposet, "Symmetries",
          [
           "compute Aut",
           "compute cAut/Aut",
           "compute aAut"
           ],
          [
           "forsubset",
           "forsubset",
           "forsubset"
           ],
          [
           # compute Aut
           function(gpos,menu,entry)
        local sel,v,node,idx,i;
        
        sel:=Selected(gpos);
        for v in sel do
            node:=v!.data;
            idx:=Position(node!.nodeInfo.names,"Aut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for i in [1..Length(node!.nodeInfo.names)] do
                updater(node,i);
            od;
            ReshapeAll@(gpos);
        od;
    end,
      # compute cAut/Aut
      function(gpos,menu,entry)
        local sel,v,node,idx,i;
        
        sel:=Selected(gpos);
        for v in sel do
            node:=v!.data;
            idx:=Position(node!.nodeInfo.names,"cAut/Aut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for i in [1..Length(node!.nodeInfo.names)] do
                updater(node,i);
            od;
        od;
    end,
      # compute aAut
      function(gpos,menu,entry)
        local sel,v,node,idx,i;
        
        sel:=Selected(gpos);
        for v in sel do
            node:=v!.data;
            idx:=Position(node!.nodeInfo.names,"aAut:");
            if idx <> fail then
                setter(node,idx);
            fi;
            for i in [1..Length(node!.nodeInfo.names)] do
                updater(node,i);
            od;
        od;
    end
      ]);

    Menu( gposet, "Selection",
          [
           "Select Green",
           "Invert Selection",,
           "Report..."
           ],
          [
           "forany",
           "forany",,
           "forsubset"
           ],
          [
        # select green
           function(gpos, menu, entry)
        local sel,V;
        sel:=gpos!.lastresult;
        DeselectAll(gpos);
        ClearGreen@( gpos );
        
        for V in sel do
            Select( gpos, V );
        od;
    end,
      # invert selection
      function(gpos,menu,entry)
        local sel,lev,class,vert;
        sel:=Selected(gpos);
        DeselectAll(gpos);
        for lev in Levels( gpos ) do
            for class in Classes( gpos, lev ) do
                for vert in Vertices( gpos, lev, class ) do
                    if not( vert in sel ) then
                        Select(gpos,vert);
                    fi;
                od;
            od;
        od;
    end,,
      # report
      function(gpos,menu,entry)
        local sel,di,res,v,node,ninf,i,pos,strictupperbounds,maxin,maxlength,indices,index,algtwins,cgr,str;
        
        sel:=Selected(gpos);
        SortBy(sel, v->IndexOfCocoNode(v!.data));
        indices:=List(sel, x->IndexOfCocoNode(x!.data));
        
        di := Dialog("Filename","Log File?");
        res:= Query(di,"coco2p.info");
        
        if res <> false then
            PrintTo(res,"COCO2P - Informations about a PosetOfFusionOrbits\n",
                    "-------------------------------------------------\n");
            if sel<>[] then
                cgr:=sel[1]!.data!.poset!.cgr;
                
                node:=NewCocoNode(cgr);
                RegisterStandardInfo@(node);

                ComputeAllInfos(node);
                for str in infoOptions@.disabled do
                    ComputeInfo(node,str);
                od;
                AppendTo(res, NodeInfoString(node));
                AppendTo(res, "-------------------------------------------------\n");
            fi;
            
            for v in sel do
                node:=v!.data;
                ninf:=node!.nodeInfo;
                maxlength:=Maximum(ninf.maxlength, 20);
                index:=IndexOfCocoNode(node);
                AppendTo(res, NodeInfoString(node));
                pos:=node!.poset;
                algtwins:=Intersection(pos!.algTwins[index], indices);
                if algtwins<>[] then
                    AppendTo(res, String("Algebraic Twins: ",-maxlength), algtwins,"\n");
                fi;
                strictupperbounds:=Difference(FilterInCocoPoset(pos,index),[index]);
                strictupperbounds:=Intersection(strictupperbounds,indices);
                maxin:=[];
                if strictupperbounds<>[] then
                    maxin:=MinimalElementsInCocoPoset(pos,strictupperbounds);
                fi;
                AppendTo(res, String("Maximal Merging in: ",-maxlength), maxin,"\n");
                AppendTo(res,"\n");
            od;
        fi;
        end]);


  # close text selector
    funcclose := function( sel, bt )
        gposet!.infobox := false;
        Close(sel);
        return true;
    end;

    funcall := function( sel, bt )
        local i;
        for i  in [ 1 .. Length(sel!.labels) ]  do
            sel!.selected := i;
            sel!.textFuncs[i]( sel, sel!.labels[i] );
        od;
        Enable( sel, "all", false );
        return true;
    end;

    updater:=function(node,i)
        local val;
        
        if node!.nodeInfo.values[i]<>"unknown" then
            return;
        fi;
        if node!.nodeInfo.testers[i](node) then
            val:=node!.nodeInfo.getters[i](node);
            if val <> fail then
                node!.nodeInfo.values[i]:=node!.nodeInfo.toStr[i](val);
            fi;
        fi;
    end;
    
    setter:=function(node,i)
        local val;
        
        if node!.nodeInfo.values[i]<>"unknown" then
            return;
        fi;
        val:=node!.nodeInfo.getters[i](node);
        if val <> fail then
            node!.nodeInfo.values[i]:=node!.nodeInfo.toStr[i](val);
        fi;
    end;

    
    InstallPopup( gposet,
    function( sheet, vert, x, y )
	local id, texts,node;

        if sheet!.infobox <> false then
            Close(sheet!.infobox);
            sheet!.infobox := false;
        fi;

        if vert=fail then
            PopupFromMenu(sheet!.menus[3]);
            return;
        fi;
        node:=vert!.data;

        texts:=[];
        for i in [1..Length(node!.nodeInfo.names)] do
            updater(node,i);
            Add(texts, Concatenation(String(node!.nodeInfo.names[i],-node!.nodeInfo.maxlength), node!.nodeInfo.values[i]));
            Add(texts, function(x,y)
                local ret,i;

                ret:=node!.nodeInfo.getters[x!.selected](node);
                if ret <> fail then
                    node!.nodeInfo.values[x!.selected]:=node!.nodeInfo.toStr[x!.selected](ret);
                fi;
                

                for i in [1..Length(node!.nodeInfo.names)] do
                    updater(node,i);
                    Relabel(x,i,Concatenation(String(node!.nodeInfo.names[i],-node!.nodeInfo.maxlength),node!.nodeInfo.values[i]));
                od;

                Reshape( gposet, vert);
                return ret;
            end);
        od;

        sheet!.infobox := TextSelector(
        Concatenation( "Information on color graph ",vert!.label ),
        texts,
	[ "all", funcall, "close", funcclose ] );
    end);
    return gposet;
end);


InstallMethod(SelectedElements,
        "for graphic coco posets",
        [IsGraphicCocoPoset],
function(gpos)
    local sel;

    sel:=Selected(gpos);

    return Set(sel, v->IndexOfCocoNode(v!.data));
end);
