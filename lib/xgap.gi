# BindGlobal( "ClearGreenColor",
#   function( latt )
#   local lev, class, vert, sel;
#     sel := Selected( latt );
#     for lev in Levels( latt ) do
#       for class in Classes( latt, lev ) do
#         for vert in Vertices( latt, lev, class ) do
# 	  if not( vert in sel ) then
# 		Recolor( latt, vert, COLORS.black );
# 	  fi;
# 	od;
#       od;
#     od;
# end );
 

InstallMethod(
	ChooseShape,
	"for Graphic cgr iso posets",
	[IsGraphicPosetRep and IsGraphicCgrIsoPoset,IsRecord],
function( cgrposet, data )
  local cgr;
    cgr := data.cgr;
    if HasIsSchurian( cgr ) then
        if IsSchurian( cgr ) then
            return "circle"; 
        else
            return "diamond";
        fi;
    else
        return "rectangle";
    fi;
end );

InstallMethod(ChooseLevel,
	"for Graphic COCO-posets",
	[IsGraphicPosetRep and IsGraphicCocoPoset, IsRecord],
function( cocoposet, data )
    return data.level;
end );

InstallMethod(ChooseLevel,
	"for Graphic cgr iso posets",
	[IsGraphicPosetRep and IsGraphicCgrIsoPoset, IsRecord],
function( cgrposet, data )
    return RankOfColorGraph( data.cgr );
end );

InstallMethod(
	CompareLevels,
	"for cgr iso posets",
	[ IsGraphicPosetRep and IsGraphicCgrIsoPoset, IsInt, IsInt ],
function( poset, a, b )
    if a < b then
	return 1;
    elif a > b then
	return -1;
    else
	return 0;
    fi;
end);

InstallMethod(
	CompareLevels,
	true,
	[ IsGraphicPosetRep and IsGraphicCocoPoset, IsInt, IsInt ],
	0,
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
    local   gposet,  vertices,  i,  elm,  j,  lev;
    
    gposet := GraphicPoset( "COCO-poset", 800, 600 );

    SetFilterObj( gposet, IsGraphicCocoPoset );

    vertices := [];
    for i in [1..Size(cocoposet)] do
        elm:=ElementsOfCocoPoset(cocoposet)[i];
        lev:=Length(IdealInCocoPoset(cocoposet,i));
        
	CreateLevel( gposet, lev);
	Add( vertices, Vertex( gposet, rec( element := elm, level := lev),  
			rec( label := String( i )
			) ) ); 
    od;
    for i in [1..Size(cocoposet)] do
      for j in SuccessorsInCocoPoset(cocoposet,i) do
	Edge( gposet, vertices[i], vertices[j] );
      od;
    od;
    return gposet;
end);


InstallMethod(GraphicCocoPoset,
        "for Sub Iso Lattices",
        [IsCocoPoset and IsSubIsoLattice],
function(cgrposet)
    local gposet,cgr,i,j,vertices,funcclose;
    
    gposet := GraphicPoset( "Iso-poset of color graphs", 800, 600 );

    SetFilterObj( gposet, IsGraphicCgrIsoPoset );

    vertices := [];
    for i in [1..Size(cgrposet)] do
        cgr:=ElementsOfCocoPoset(cgrposet)[i];
	CreateLevel( gposet, RankOfColorGraph(cgr) );
	Add( vertices, Vertex( gposet, rec( cgr := cgr ), 
			rec( label := String( i )
			) ) ); 
    od;
    for i in [1..Size(cgrposet)] do
      for j in SuccessorsInCocoPoset(cgrposet,i) do
	Edge( gposet, vertices[i], vertices[j] );
      od;
    od;

    # Menu( latt, "Ideals", 
    #     [
    #     "Intersection",
    #     "Closure",
    #     "Commutator",
    #     "Covers",
    #     "Subcovers",
    #     "Ideal type",
    #     ], 
    #     [
    #     "forsubset",
    #     "forsubset",
    #     "forsubset",
    #     "forone",
    #     "forone",
    #     "forsubset"
    #     ], 
    #     [
    #     # Intersection
    #     function(arg)
    #       local sel, C, latt;
    #         latt := arg[1];
    #         sel := Selected( latt );
    #         C := Intersection( List( sel, I -> I!.data.ideal ) );
    #         C := WhichVertex( latt, C, 
    #     	function( N, R ) return R.ideal = N; end ); 
    #         ClearGreen( latt );
    #         Recolor( latt, C, COLORS.green ); 
    #     end,

    #     # Closure
    #     function(arg)
    #       local sel, I, C, latt;
    #         latt := arg[1];
    #         sel := Selected( latt );
    #         sel := List( sel, I -> I!.data.ideal );
    #         C := sel[1];
    #         for I in sel{[2..Length(sel)]} do
    #           C := ClosureNearRingIdeal( C, I );
    #         od;
    #         C := WhichVertex( latt, C, 
    #     	function( N, R ) return R.ideal = N; end ); 
    #         ClearGreen( latt );
    #         Recolor( latt, C, COLORS.green ); 
    #     end,

    #     # Commutator
    #     function(arg) 
    #       local sel, I, J, C, latt;
    #         latt := arg[1];
    #         sel := Selected( latt );
    #         if Length( sel )=1 then
    #     	I := sel[1]; J := sel[1];
    #         elif Length( sel )=2 then
    #             I := sel[1]; J := sel[2];
    #         else
    #     	return;
    #         fi;
    #         C := NearRingCommutator(I!.data.ideal,J!.data.ideal);
    #         C := WhichVertex( latt, C, 
    #     	function( N, R ) return R.ideal = N; end ); 
    #         ClearGreen( latt );
    #         Recolor( latt, C, COLORS.green ); 
    #     end,

    #     # Covers
    #     function(arg)
    #       local V, I, Cs, latt;
    #         latt := arg[1];
    #         I := Selected(latt)[1];
    #         Cs := MaximalIn( latt, I );
    #         ClearGreen( latt );
    #         for V in Cs do
    #           Recolor( latt, V, COLORS.green ); 
    #         od;
    #     end,

    #     # Subcovers
    #     function(arg)
    #       local V, I, Cs, latt;
    #         latt := arg[1];
    #         I := Selected(latt)[1];
    #         Cs := Maximals( latt, I );
    #         ClearGreen( latt );
    #         for V in Cs do
    #           Recolor( latt, V, COLORS.green ); 
    #         od;
    #     end,

    #     # Ideal type
    #     function(arg)
    #     local latt, sel, vert;
    #       latt := arg[1];
    #       sel := Selected( latt ); 
    #       for vert in sel do
    #         if IsNearRingIdeal( vert!.data.ideal ) then
    #     	Reshape( latt, vert, "circle" );
    #         fi;
    #       od;
    #     end
    #     ] );

  # close text selector
    funcclose := function( sel, bt )
        Close(sel);
        return true;  
    end;

    InstallPopup( gposet,
    function( sheet, vert, x, y )
	local id, text;
        #          text := Concatenation( "LibraryNearRing( ",Name(id[1]),", ",String(id[2])," )");
        sheet!.infobox := TextSelector( 
        Concatenation( "Information on color graph ",vert!.label ), 
        [ 
        "Order : ",
        function(x,y) 
            Relabel( x, 1, Concatenation( "Order : ", String(Order(vert!.data.cgr)) ) );
            return Order(vert!.data.cgr); 
	end,

        "Rank : ",
        function(x,y) 
            Relabel( x, 2, Concatenation( "Rank : ", String(Rank(vert!.data.cgr)) ) );
            return Rank(vert!.data.cgr); 
	end,
   
        "Is Schurian : ",
	function(x,y)
	  Relabel( x, 3, Concatenation( "Is Schurian : ",
                  String( IsSchurian( vert!.data.cgr ) ) ) );
          Reshape( gposet, vert);

	  return IsSchurian( vert!.data.cgr );
	end,

        "Is homogeneous : ",
	function(x,y)
	  Relabel( x, 4, Concatenation( "Is homogeneous : ",
                  String( IsHomogeneous( vert!.data.cgr ) ) ) );

	  return IsHomogeneous( vert!.data.cgr );
	end,
   
        "Is primitive : ",
	function(x,y)
	  Relabel( x, 5, Concatenation( "Is primitive : ",
                  String( IsPrimitive( vert!.data.cgr ) ) ) );

	  return IsPrimitive( vert!.data.cgr );
	end,
   
        #   "Factor isomorphic to",
	# function(x,y)
	# local factor, id; 
	#   factor := FactorNearRing( Parent(vert!.data.ideal),
	# 				vert!.data.ideal );
	#   if Size(factor) > 15 then
	# 	return factor;
	#   else
	# 	id := IdLibraryNearRing( factor );
	# 	Relabel( x, 3, Concatenation( "Factor isomorphic to ", 
	# 	"LibraryNearRing( ",Name(id[1]),", ",String(id[2])," )") );
	# 	return factor;
	#   fi;
	# end,

	  "Export color graph to GAP", 
	function(x,y) return vert!.data.cgr; end
	], 

	[ "close", funcclose ] );
	end
	);
     return gposet;
 end);

