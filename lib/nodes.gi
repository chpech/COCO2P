

CocoNodesFam := NewFamily("CocoNodesFam", IsCocoNode);

DeclareRepresentation("IsCocoNodeRep",
        IsAttributeStoringRep,
        [ "poset",
          "index",
          "level"]
        );

InstallMethod(ShapeOfCocoNode,
        "for coco nodes",
        [IsCocoNode],
function(node)
    return "rectangle";
end);

InstallMethod(LevelOfCocoNode,
	"for coco nodes in CocoNodeRep",
	[IsCocoNode and IsCocoNodeRep],
function(node)
    return node!.level;
end );

InstallMethod(IndexOfCocoNode,
        "for coco nodes in CocoNodeRep",
        [IsCocoNode and IsCocoNodeRep],
function(node)
    return node!.index;
end);

DeclareRepresentation("IsColorGraphNodeRep",
        IsCocoNodeRep,
        [ "poset",
          "index",
          "level",
          "cgr",
          "nodeInfo"]
        );
    
InstallMethod(
	ShapeOfCocoNode,
	"for coco nodes in ColorGraphNodeRep",
	[IsCocoNode and IsColorGraphNodeRep],
function(node)
    local cgr;
    cgr := node!.cgr;
    if RankOfColorGraph(cgr)=2 then
        return "circle";
    fi;
    if RankOfColorGraph(cgr)=3 and not IsPrimitiveColorGraph(cgr) then
        return "circle";
    fi;
    
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

InstallMethod(
	LevelOfCocoNode,
	"for coco nodes in ColorGraphNodeRep",
	[IsCocoNode and IsColorGraphNodeRep],
function(node)
    return RankOfColorGraph(node!.cgr);
end);

InstallMethod(ComputeInfo,
        "for coco nodes in ColorGraphNodeRep",
	[IsCocoNode and IsColorGraphNodeRep, IsString],
function(node,str)
    local pos;
    
    pos:=Position(node!.nodeInfo.names,str);
    if pos=fail then
        return fail;
    fi;
    if node!.nodeInfo.values[pos]="unknown" then
        node!.nodeInfo.values[pos]:=node!.nodeInfo.toStr[pos](node!.nodeInfo.getters[pos](node));
    fi;
    
    return true;
end);

InstallMethod(ComputeAllInfos,
        "for coco nodes in ColorGraphNodeRep",
	[IsCocoNode and IsColorGraphNodeRep],
function(node)
    local pos,i,str;
    
    for i in [1..Length(node!.nodeInfo.names)] do
        str:=node!.nodeInfo.names[i];
        if node!.nodeInfo.values[i]="unknown" and 
           not str in infoOptions@.disabled then
            ComputeInfo(node,str);
        fi;
    od;
end);

StringMultiset:=function(s)
    local cs,e,str,res;
    
    res:="";
    str:=OutputTextString(res,true);
    cs:=Collected(s);
    for e in cs do
        if e[2]=1 then
            PrintTo(str,e[1]);
        else
            PrintTo(str,e[1],"^",e[2]);
        fi;
        if e<>cs[Length(cs)] then
            PrintTo(str,",");
        fi;
    od;
    CloseStream(str);
    return res;
end;

              
InstallOtherMethod(NewCocoNode,
        "for color graphs",
        [IsColorGraph and IsWLStableColorGraph],
function(cgr)
    local tensor,nodeInfo, register;
    
    nodeInfo:=rec(names:=[],
                  values:=[],
                  testers:=[],
                  toStr:=[],
                  getters:=[],
                  maxlength:=0);
    register:=function(info)
        Add(nodeInfo.names,info.name);
        Add(nodeInfo.values,"unknown");
        Add(nodeInfo.testers,info.tester);
        Add(nodeInfo.toStr,info.toStr);
        Add(nodeInfo.getters,info.getter);
        if Length(info.name)+1>nodeInfo.maxlength then
            nodeInfo.maxlength:=Length(info.name)+1;
        fi;
    end;
    tensor:=StructureConstantsOfColorGraph(cgr);
    
    register(rec(name:="order:",toStr:=String,tester:=node->true,getter:=node->OrderOfColorGraph(node!.cgr)));
    register(rec(name:="rank:",toStr:=String,tester:=node->true,getter:=node->RankOfColorGraph(node!.cgr)));
    if RankOfColorGraph(cgr)=3 then
        if Mates(tensor)=() then
            register(rec(name:="srg:", 
                    toStr:=vklm->Concatenation("(",String(vklm[1]),",",String(vklm[2]),",",String(vklm[3]),",",String(vklm[4]),")"),
                           tester:=node->true,getter:=function(node) local srg_I,srg_k,srg_A,srg_JIA,srg_lambda,srg_mu,tensor;
                srg_I:=ReflexiveColors(node!.cgr)[1];
                srg_k:=Minimum(OutValencies(node!.cgr)
                               {Difference([1..Rank(node!.cgr)],
                                       [srg_I])});
                srg_A:=First([1..Rank(node!.cgr)], x->OutValencies(node!.cgr)[x]=srg_k);
                srg_JIA:=Difference([1..3],Set([srg_I,srg_A]))[1];
                tensor:=StructureConstantsOfColorGraph(node!.cgr);
                srg_lambda:=tensor[[srg_A,srg_A,srg_A]];
                srg_mu:=tensor[[srg_A,srg_A,srg_JIA]];
                return [OrderOfColorGraph(node!.cgr), srg_k, srg_lambda, srg_mu];
            end));
        else
            register(rec(name:="type:",toStr:=x->x,tester:=node->true,getter:=node->"doubly regular tournament"));
        fi;
    fi;
    
    if RankOfColorGraph(cgr)>3 then
        if IsHomogeneous(cgr) then 
            register(rec(name:="valencies:", toStr:=StringMultiset, tester:=node->true,getter:=node->OutValencies(StructureConstantsOfColorGraph(node!.cgr))));
        else
            register(rec(name:="# of fibres:", toStr:=String, tester:=node->true,getter:=node->NumberOfFibres(node!.cgr)));
        fi;
    fi;
    
    if RankOfColorGraph(cgr)>2 and (RankOfColorGraph(cgr)>3 or IsPrimitiveColorGraph(cgr)) then
        register(rec(name:="Schurian", toStr:=String,tester:=node->HasAutGroupOfCocoObject(node!.cgr),getter:=node->IsSchurian(node!.cgr)));
    fi;
    if IsHomogeneous(cgr) and RankOfColorGraph(cgr)>3 then
        register(rec(name:="primitive:",toStr:=String,tester:=node->true,getter:=node->IsPrimitiveColorGraph(node!.cgr)));
        register(rec(name:="symmetric:",toStr:=String,tester:=node->true,getter:=node->IsSymmetricColorGraph(node!.cgr)));
        register(rec(name:="commutative:",toStr:=String,tester:=node->true,getter:=node->IsCommutativeTensor(StructureConstantsOfColorGraph(node!.cgr))));
    fi;
    
    if RankOfColorGraph(cgr)>2 and (RankOfColorGraph(cgr)>3 or IsPrimitiveColorGraph(cgr)) then
        register(rec(name:="order(Aut):",toStr:=StringPP,tester:=node->HasAutGroupOfCocoObject(node!.cgr),getter:=node->Order(AutGroupOfCocoObject(node!.cgr))));
        register(rec(name:="Aut:",toStr:=String,tester:=node->HasAutGroupOfCocoObject(node!.cgr) and HasStructureDescription(AutGroupOfCocoObject(node!.cgr)),getter:=node->StructureDescription(AutGroupOfCocoObject(node!.cgr):short)));
        register(rec(name:="order(cAut/Aut):", toStr:=StringPP,tester:=node->HasColorAutomorphismGroupOnColors(node!.cgr),getter:=node->Order(ColorAutomorphismGroupOnColors(node!.cgr))));
        register(rec(name:="cAut/Aut:",toStr:=String,tester:=node->HasColorAutomorphismGroupOnColors(node!.cgr),getter:=node->StructureDescription(ColorAutomorphismGroupOnColors(node!.cgr):short)));
        register(rec(name:="[aAut:cAut/Aut]:", toStr:=StringPP, tester:=node->HasAlgebraicAutomorphismGroup(node!.cgr) and HasColorAutomorphismGroupOnColors(node!.cgr),getter:=node->Order(AlgebraicAutomorphismGroup(node!.cgr))/Order(ColorAutomorphismGroupOnColors(node!.cgr))));
        register(rec(name:="aAut:", toStr:=String, tester:=node->HasAlgebraicAutomorphismGroup(node!.cgr),getter:=node->StructureDescription(AlgebraicAutomorphismGroup(node!.cgr):short)));
    fi;
    
        
    return Objectify(NewType(CocoNodesFam, IsCocoNode and IsColorGraphNodeRep),
                   rec( poset:=fail,
                        index:=0,
                        level:=RankOfColorGraph(cgr),
                        cgr:=cgr,
                        nodeInfo:=nodeInfo));
end);


InstallMethod(NewCocoNode,
        "for SubColorIsomorphismPosets and positive integers",
        [IsSubColorIsomorphismPoset and IsSubColorIsomorphismPosetRep, IsPosInt],
function(poset,index)
    local cgr,nodeInfo,register,tensor;
    cgr:=poset!.elements[index];
    tensor:=StructureConstantsOfColorGraph(cgr);


    nodeInfo:=rec(names:=[],
                  values:=[],
                  testers:=[],
                  toStr:=[],
                  getters:=[],
                  maxlength:=0);
    register:=function(info)
        Add(nodeInfo.names,info.name);
        Add(nodeInfo.values,"unknown");
        Add(nodeInfo.testers,info.tester);
        Add(nodeInfo.toStr,info.toStr);
        Add(nodeInfo.getters,info.getter);
        if Length(info.name)+1>nodeInfo.maxlength then
            nodeInfo.maxlength:=Length(info.name)+1;
        fi;
    end;
    
    register(rec(name:="Number:", toStr:=String,tester:=node->true,getter:=node->node!.index));
    register(rec(name:="order:",toStr:=String,tester:=node->true,getter:=node->OrderOfColorGraph(node!.cgr)));
    register(rec(name:="rank:",toStr:=String,tester:=node->true,getter:=node->RankOfColorGraph(node!.cgr)));
    if RankOfColorGraph(cgr)=3 then
        if Mates(tensor)=() then
            register(rec(name:="srg:", toStr:=vklm->Concatenation("(",String(vklm[1]),",",String(vklm[2]),",",String(vklm[3]),",",String(vklm[4]),")"),tester:=node->true,getter:=function(node) local srg_I,srg_k,srg_A,srg_JIA,srg_lambda,srg_mu,tensor;
                srg_I:=ReflexiveColors(node!.cgr)[1];
                srg_k:=Minimum(OutValencies(node!.cgr)
                               {Difference([1..Rank(node!.cgr)],
                                       [srg_I])});
                srg_A:=First([1..Rank(node!.cgr)], x->OutValencies(node!.cgr)[x]=srg_k);
                srg_JIA:=Difference([1..3],Set([srg_I,srg_A]))[1];
                tensor:=StructureConstantsOfColorGraph(node!.cgr);
                srg_lambda:=tensor[[srg_A,srg_A,srg_A]];
                srg_mu:=tensor[[srg_A,srg_A,srg_JIA]];
                return [OrderOfColorGraph(node!.cgr), srg_k, srg_lambda, srg_mu];
            end));
        else
            register(rec(name:="type:",toStr:=x->x,tester:=node->true,getter:=node->"doubly regular tournament"));
        fi;
    fi;

    if RankOfColorGraph(cgr)>3 then
        register(rec(name:="valencies:", toStr:=StringMultiset, tester:=node->true,getter:=node->OutValencies(StructureConstantsOfColorGraph(node!.cgr))));
    fi;

    if RankOfColorGraph(cgr)>2 and (RankOfColorGraph(cgr)>3 or IsPrimitiveColorGraph(cgr)) then
        register(rec(name:="Schurian", toStr:=String,tester:=node->HasAutGroupOfCocoObject(node!.cgr),getter:=node->IsSchurian(node!.cgr)));
    fi;
    
    if IsHomogeneous(cgr) and RankOfColorGraph(cgr)>3 then
        register(rec(name:="primitive:",toStr:=String,tester:=node->true,getter:=node->IsPrimitiveColorGraph(node!.cgr)));
        register(rec(name:="symmetric:",toStr:=String,tester:=node->true,getter:=node->IsSymmetricColorGraph(node!.cgr)));
        register(rec(name:="commutative:",toStr:=String,tester:=node->true,getter:=node->IsCommutativeTensor(StructureConstantsOfColorGraph(node!.cgr))));
    fi;
    if RankOfColorGraph(cgr)>2 and (RankOfColorGraph(cgr)>3 or IsPrimitiveColorGraph(cgr)) then
        register(rec(name:="order(Aut):",toStr:=StringPP,tester:=node->HasAutGroupOfCocoObject(node!.cgr),getter:=node->Order(AutGroupOfCocoObject(node!.cgr))));
        register(rec(name:="Aut:",toStr:=String,tester:=node->HasAutGroupOfCocoObject(node!.cgr) and HasStructureDescription(AutGroupOfCocoObject(node!.cgr)),getter:=node->StructureDescription(AutGroupOfCocoObject(node!.cgr):short)));
        register(rec(name:="order(cAut/Aut):", toStr:=StringPP,tester:=node->HasColorAutomorphismGroupOnColors(node!.cgr),getter:=node->Order(ColorAutomorphismGroupOnColors(node!.cgr))));
        register(rec(name:="cAut/Aut:",toStr:=String,tester:=node->HasColorAutomorphismGroupOnColors(node!.cgr),getter:=node->StructureDescription(ColorAutomorphismGroupOnColors(node!.cgr):short)));
        register(rec(name:="[aAut:cAut/Aut]:", toStr:=StringPP, tester:=node->HasAlgebraicAutomorphismGroup(node!.cgr) and HasColorAutomorphismGroupOnColors(node!.cgr),getter:=node->Order(AlgebraicAutomorphismGroup(node!.cgr))/Order(ColorAutomorphismGroupOnColors(node!.cgr))));
        register(rec(name:="aAut:", toStr:=String, tester:=node->HasAlgebraicAutomorphismGroup(node!.cgr),getter:=node->StructureDescription(AlgebraicAutomorphismGroup(node!.cgr):short)));
    fi;

    return Objectify(NewType(CocoNodesFam, IsCocoNode and IsColorGraphNodeRep),
                   rec( poset:=poset,
                        index:=index,
                        level:=RankOfColorGraph(cgr),
                        cgr:=cgr,
                        nodeInfo:=nodeInfo));
end);

InstallMethod(NewCocoNode,
        "for posets of fusion orbits and positive integers",
        [IsPosetOfFusionOrbits and IsPosetOfFusionOrbitsRep, IsPosInt],
function(poset,index)
    local cgr,fusion,nodeInfo,register,tensor;
    cgr:=poset!.colorGraphs[index];
    fusion:=poset!.elements[index];
    tensor:=StructureConstantsOfColorGraph(cgr);


    nodeInfo:=rec(names:=[],
                  values:=[],
                  testers:=[],
                  toStr:=[],
                  getters:=[],
                  maxlength:=0);
    register:=function(info)
        Add(nodeInfo.names,info.name);
        Add(nodeInfo.values,"unknown");
        Add(nodeInfo.testers,info.tester);
        Add(nodeInfo.toStr,info.toStr);
        Add(nodeInfo.getters,info.getter);
        if Length(info.name)+1>nodeInfo.maxlength then
            nodeInfo.maxlength:=Length(info.name)+1;
        fi;
    end;
    
    register(rec(name:="Number:", toStr:=String,tester:=node->true,getter:=node->node!.index));
    register(rec(name:="order:",toStr:=String,tester:=node->true,getter:=node->OrderOfColorGraph(node!.cgr)));
    register(rec(name:="rank:",toStr:=String,tester:=node->true,getter:=node->RankOfColorGraph(node!.cgr)));
    register(rec(name:="orbit size:", toStr:=String,tester:=node->true,getter:=node->Size(node!.poset!.elements[node!.index])));
    if RankOfColorGraph(cgr)=3 then
        if Mates(tensor)=() then
            register(rec(name:="srg:", toStr:=vklm->Concatenation("(",String(vklm[1]),",",String(vklm[2]),",",String(vklm[3]),",",String(vklm[4]),")"),tester:=node->true,getter:=function(node) local srg_I,srg_k,srg_A,srg_JIA,srg_lambda,srg_mu,tensor;
                srg_I:=ReflexiveColors(node!.cgr)[1];
                srg_k:=Minimum(OutValencies(node!.cgr)
                               {Difference([1..Rank(node!.cgr)],
                                       [srg_I])});
                srg_A:=First([1..Rank(node!.cgr)], x->OutValencies(node!.cgr)[x]=srg_k);
                srg_JIA:=Difference([1..3],Set([srg_I,srg_A]))[1];
                tensor:=StructureConstantsOfColorGraph(node!.cgr);
                srg_lambda:=tensor[[srg_A,srg_A,srg_A]];
                srg_mu:=tensor[[srg_A,srg_A,srg_JIA]];
                return [OrderOfColorGraph(node!.cgr), srg_k, srg_lambda, srg_mu];
            end));
        else
            register(rec(name:="type:",toStr:=x->x,tester:=node->true,getter:=node->"doubly regular tournament"));
        fi;
    fi;

    if RankOfColorGraph(cgr)>3 then
        register(rec(name:="valencies:", toStr:=StringMultiset, tester:=node->true,getter:=node->OutValencies(StructureConstantsOfColorGraph(node!.cgr))));
    fi;

    if RankOfColorGraph(cgr)>2 and (RankOfColorGraph(cgr)>3 or IsPrimitiveColorGraph(cgr)) then
        register(rec(name:="Schurian", toStr:=String,tester:=node->HasAutGroupOfCocoObject(node!.cgr),getter:=node->IsSchurian(node!.cgr)));
        register(rec(name:="primitive:",toStr:=String,tester:=node->true,getter:=node->IsPrimitiveColorGraph(node!.cgr)));
        register(rec(name:="symmetric:",toStr:=String,tester:=node->true,getter:=node->IsSymmetricColorGraph(node!.cgr)));
        register(rec(name:="commutative:",toStr:=String,tester:=node->true,getter:=node->IsCommutativeTensor(StructureConstantsOfColorGraph(node!.cgr))));
        register(rec(name:="order(Aut):",toStr:=StringPP,tester:=node->HasAutGroupOfCocoObject(node!.cgr),getter:=node->Order(AutGroupOfCocoObject(node!.cgr))));
        register(rec(name:="Aut:",toStr:=String,tester:=node->HasAutGroupOfCocoObject(node!.cgr) and HasStructureDescription(AutGroupOfCocoObject(node!.cgr)),getter:=node->StructureDescription(AutGroupOfCocoObject(node!.cgr):short)));
        register(rec(name:="order(cAut/Aut):", toStr:=StringPP,tester:=node->HasColorAutomorphismGroupOnColors(node!.cgr),getter:=node->Order(ColorAutomorphismGroupOnColors(node!.cgr))));
        register(rec(name:="cAut/Aut:",toStr:=String,tester:=node->HasColorAutomorphismGroupOnColors(node!.cgr),getter:=node->StructureDescription(ColorAutomorphismGroupOnColors(node!.cgr):short)));
        register(rec(name:="[aAut:cAut/Aut]:", toStr:=StringPP, tester:=node->HasAlgebraicAutomorphismGroup(node!.cgr) and HasColorAutomorphismGroupOnColors(node!.cgr),getter:=node->Order(AlgebraicAutomorphismGroup(node!.cgr))/Order(ColorAutomorphismGroupOnColors(node!.cgr))));
        register(rec(name:="aAut:", toStr:=String, tester:=node->HasAlgebraicAutomorphismGroup(node!.cgr),getter:=node->StructureDescription(AlgebraicAutomorphismGroup(node!.cgr):short)));
    fi;

    register(rec(name:="algebraic:",toStr:=String,tester:=node->true,getter:=node->node!.index in node!.poset!.algebraicFusions));

    return Objectify(NewType(CocoNodesFam, IsCocoNode and IsColorGraphNodeRep),
                   rec( poset:=poset,
                        index:=index,
                        level:=RankOfColorGraph(cgr),
                        cgr:=cgr,
                        nodeInfo:=nodeInfo));
end);


InstallMethod(NodeInfoString,
        "for coco nodes in ColorGraphNodeRep",
        [IsCocoNode and IsColorGraphNodeRep],
function(node)
    local str,res,ninf,maxlength,i;
    
        
    str:="";
    res:=OutputTextString( str, true );;
    ninf:=node!.nodeInfo;
    maxlength:=Maximum(ninf.maxlength, 20);
    for i in [1..Length(ninf.names)] do
        if ninf.values[i]="unknown" and not ninf.names[i] in infoOptions@.disabled or node!.nodeInfo.testers[i](node) then
            ninf.values[i]:=ninf.toStr[i](ninf.getters[i](node));
        fi;
        AppendTo(res, String(ninf.names[i],-maxlength),ninf.values[i],"\n");
    od;
    CloseStream(res);
    return str;
end);

InstallMethod(UpdateInfoInCocoNode,
        "for coco nodes in ColorGraphNodeRep",
        [IsCocoNode and IsColorGraphNodeRep,IsString],
function(node,str)
    local pos;
    
    pos:=Position(node!.nodeInfo.names,str);
    if pos=fail then
        return fail;
    fi;
    if node!.nodeInfo.values[pos]<>"unknown" then
        return;
    fi;
    if node!.nodeInfo.testers[pos](node) then
        node!.nodeInfo.values[pos]:=node!.nodeInfo.toStr[pos](node!.nodeInfo.getters[pos](node));
    fi;
end);
