

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
    local pos,val;
    
    pos:=Position(node!.nodeInfo.names,str);
    if pos=fail then
        return fail;
    fi;
    if node!.nodeInfo.values[pos]="unknown" then
        val:=node!.nodeInfo.getters[pos](node);
        if val<>fail then
            node!.nodeInfo.values[pos]:=node!.nodeInfo.toStr[pos](val);
        fi;
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

StringMultiset@:=function(s)
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

StringList@:=function(s)
    local  res, str, e;
    
    res:="";
    str:=OutputTextString(res,true);
    for e in s do
        PrintTo(str,e);
        if e<>s[Length(s)] then
            PrintTo(str,",");
        fi;
    od;
    CloseStream(str);
    return res;
end;

GetParams@:=function(tensor,ord)
    local  d, bi, ci;
    
    d:=Order(tensor)-1;
    bi:=List([0..d-1], i->EntryOfTensor(tensor, ord[i+2],ord[2],ord[i+1]));
    ci:=List([1..d], i->EntryOfTensor(tensor, ord[i],ord[2],ord[i+1]));
    return [bi,ci];
end;

StringParams@:=function(prm)
    local  bi,ci,res, str, i;
    
    bi:=prm[1];
    ci:=prm[2];
    
    res:="";
    str:=OutputTextString(res,true);
    PrintTo(str,"(");
    for i in [1..Length(bi)] do
        PrintTo(str, bi[i]);
        if i < Length(bi) then
            PrintTo(str,",");
        fi;
    od;
    PrintTo(str,";");
    for i in [1..Length(ci)] do
        PrintTo(str, ci[i]);
        if i < Length(ci) then
            PrintTo(str,",");
        fi;
    od;
    PrintTo(str, ")");
    CloseStream(str);
    return res;
end;

InstallMethod( RegisterInfoCocoNode,
               "for  coco nodes in ColorGraphNodeRep",
               [IsCocoNode and IsColorGraphNodeRep, IsRecord],
function(node,info)
    Add(node!.nodeInfo.names,info.name);
    
    if not IsBound(info.value) then
        Add(node!.nodeInfo.values,"unknown");
    else
        Add(node!.nodeInfo.values, info.value);
    fi;
    if not IsBound(info.tester) then
        Add(node!.nodeInfo.testers,node->true);
    else
        Add(node!.nodeInfo.testers,info.tester);
    fi;
    
    if not IsBound(info.toStr) then
        Add(node!.nodeInfo.toStr, String);
    else
        Add(node!.nodeInfo.toStr,info.toStr);
    fi;
    if not IsBound(info.getter) then
        Add(node!.nodeInfo.getters, node->fail);
    else
        Add(node!.nodeInfo.getters,info.getter);
    fi;
    
    if Length(info.name)+1>node!.nodeInfo.maxlength then
        node!.nodeInfo.maxlength:=Length(info.name)+1;
    fi;
end);

RegisterStandardInfo@:=function(node)
    local cgr,tensor,ppolord,i,key,ord;
    cgr:=node!.cgr;
    tensor:=StructureConstantsOfColorGraph(cgr);
    
    RegisterInfoCocoNode(node,rec(name:="order:",
                                  getter:=node->OrderOfColorGraph(node!.cgr)));
    RegisterInfoCocoNode(node,rec(name:="rank:",
                                  getter:=node->RankOfColorGraph(node!.cgr)));
    if RankOfColorGraph(cgr)=3 then
        if Mates(tensor)=() then
            RegisterInfoCocoNode(node,rec(name:="srg:", 
                                          toStr:=vklm->Concatenation("(",String(vklm[1]),",",String(vklm[2]),",",String(vklm[3]),",",String(vklm[4]),")"),
                                          getter:=function(node) 
                                              local srg_I,srg_k,srg_A,srg_JIA,srg_lambda,srg_mu,tensor;
                                              srg_I:=ReflexiveColors(node!.cgr)[1];
                                              srg_k:=Minimum(OutValencies(node!.cgr)
                                                                         {Difference([1..Rank(node!.cgr)], [srg_I])});
                                              srg_A:=First([1..Rank(node!.cgr)], x->OutValencies(node!.cgr)[x]=srg_k);
                                              srg_JIA:=Difference([1..3],Set([srg_I,srg_A]))[1];
                                              tensor:=StructureConstantsOfColorGraph(node!.cgr);
                                              srg_lambda:=tensor[[srg_A,srg_A,srg_A]];
                                              srg_mu:=tensor[[srg_A,srg_A,srg_JIA]];
                                              return [OrderOfColorGraph(node!.cgr), srg_k, srg_lambda, srg_mu];
                                          end));
        else
            RegisterInfoCocoNode(node,rec(name:="type:",
                                          value:="doubly regular tournament"));
        fi;
    fi;
    if RankOfColorGraph(cgr)>3 then
        ppolord:=PPolynomialOrderings(tensor);
        if ppolord<>[] then
            for i in [1..Length(ppolord)] do
                RegisterInfoCocoNode(node,rec(name:=Concatenation("P-polynomial ordering ",Concatenation(String(i),":")), 
                                              value:=StringList@(ppolord[i])));
                RegisterInfoCocoNode(node,rec(name:=Concatenation("drg-parameters ",Concatenation(String(i),":")), 
                                              toStr:=StringParams@, 
                                              value:=StringParams@(GetParams@(tensor,ppolord[i]))));
                if OutValencies(tensor)[ppolord[i][2]] > 2 then
                    RegisterInfoCocoNode(node,rec(name:=Concatenation("antipodal ", Concatenation(String(i),":")),
                                                  value:=String(IsClosedSet(tensor, Set([ppolord[i][1],ppolord[i][Length(ppolord[i])]])))));
                    RegisterInfoCocoNode(node,rec(name:=Concatenation("bipartite ", Concatenation(String(i),":")),
                                                  value:=String(IsClosedSet(tensor, ppolord[i]{Filtered([1..Order(tensor)], IsOddInt)}))));
                fi;
            od;
        fi;
    fi;
    
    if RankOfColorGraph(cgr)>3 and ppolord=[] then
        if IsHomogeneous(cgr) then 
            RegisterInfoCocoNode(node,rec(name:="valencies:", 
                                          toStr:=StringMultiset@,
                                          getter:=node->OutValencies(StructureConstantsOfColorGraph(node!.cgr))));
        else
            RegisterInfoCocoNode(node,rec(name:="# of fibres:",
                                          getter:=node->NumberOfFibres(node!.cgr)));
        fi;
    fi;
    
    if RankOfColorGraph(cgr)>2 and (RankOfColorGraph(cgr)>3 or IsPrimitiveColorGraph(cgr)) then
        RegisterInfoCocoNode(node,rec(name:="Schurian:",
                                      tester:=node->HasAutGroupOfCocoObject(node!.cgr),
                                      getter:=node->IsSchurian(node!.cgr)));
    fi;
    
    if IsHomogeneous(cgr) and RankOfColorGraph(cgr)>3 and ppolord=[] then
        RegisterInfoCocoNode(node,rec(name:="primitive:",
                                      getter:=node->IsPrimitiveColorGraph(node!.cgr)));
        RegisterInfoCocoNode(node,rec(name:="symmetric:",
                                      getter:=node->IsSymmetricColorGraph(node!.cgr)));
        RegisterInfoCocoNode(node,rec(name:="commutative:",
                                      getter:=node->IsCommutativeTensor(StructureConstantsOfColorGraph(node!.cgr))));
    fi;
    
    if RankOfColorGraph(cgr)>2 and (RankOfColorGraph(cgr)>3 or IsPrimitiveColorGraph(cgr)) then
        RegisterInfoCocoNode(node,rec(name:="order(Aut):",
                                      toStr:=StringPP,
                                      tester:=node->HasAutGroupOfCocoObject(node!.cgr),
                                      getter:=node->Order(AutGroupOfCocoObject(node!.cgr))));
        RegisterInfoCocoNode(node,rec(name:="Aut:",
                                      tester:=node->HasAutGroupOfCocoObject(node!.cgr) and HasStructureDescription(AutGroupOfCocoObject(node!.cgr)),
                                      getter:=node->StructureDescription(AutGroupOfCocoObject(node!.cgr):short)));
        RegisterInfoCocoNode(node,rec(name:="order(cAut/Aut):", 
                                      toStr:=StringPP,
                                      tester:=node->HasColorAutomorphismGroupOnColors(node!.cgr),
                                      getter:=node->Order(ColorAutomorphismGroupOnColors(node!.cgr))));
        RegisterInfoCocoNode(node,rec(name:="cAut/Aut:",
                                      tester:=node->HasColorAutomorphismGroupOnColors(node!.cgr),
                                      getter:=node->StructureDescription(ColorAutomorphismGroupOnColors(node!.cgr):short)));
        RegisterInfoCocoNode(node,rec(name:="[aAut:cAut/Aut]:", 
                                      toStr:=StringPP, 
                                      tester:=node->HasAlgebraicAutomorphismGroup(node!.cgr) and HasColorAutomorphismGroupOnColors(node!.cgr),
                                      getter:=node->Order(AlgebraicAutomorphismGroup(node!.cgr))/Order(ColorAutomorphismGroupOnColors(node!.cgr))));
        RegisterInfoCocoNode(node,rec(name:="aAut:", 
                                      tester:=node->HasAlgebraicAutomorphismGroup(node!.cgr),
                                      getter:=node->StructureDescription(AlgebraicAutomorphismGroup(node!.cgr):short)));
    fi;
end;

                   
InstallOtherMethod(NewCocoNode,
        "for color graphs",
        [IsColorGraph and IsWLStableColorGraph],
function(cgr)
    local tensor,nodeInfo, node;
    
    nodeInfo:=rec(names:=[],
                  values:=[],
                  testers:=[],
                  toStr:=[],
                  getters:=[],
                  maxlength:=0);
        
    node:=Objectify(NewType(CocoNodesFam, IsCocoNode and IsColorGraphNodeRep),
                   rec( poset:=fail,
                        index:=0,
                        level:=RankOfColorGraph(cgr),
                        cgr:=cgr,
                        nodeInfo:=nodeInfo));
    RegisterStandardInfo@(node);
    return node;
end);


InstallMethod(NewCocoNode,
        "for SubColorIsomorphismPosets and positive integers",
        [IsSubColorIsomorphismPoset and IsSubColorIsomorphismPosetRep, IsPosInt],
function(poset,index)
    local cgr,nodeInfo,node;
    cgr:=poset!.elements[index];


    nodeInfo:=rec(names:=[],
                  values:=[],
                  testers:=[],
                  toStr:=[],
                  getters:=[],
                  maxlength:=0);
    

    node:=Objectify(NewType(CocoNodesFam, IsCocoNode and IsColorGraphNodeRep),
                   rec( poset:=poset,
                        index:=index,
                        level:=RankOfColorGraph(cgr),
                        cgr:=cgr,
                        nodeInfo:=nodeInfo));
    RegisterInfoCocoNode(node, rec(name:="Number:",value:=String(node->node!.index)));
    RegisterStandardInfo@(node);
    return node;
end);

InstallMethod(NewCocoNode,
        "for posets of fusion orbits and positive integers",
        [IsPosetOfFusionOrbits and IsPosetOfFusionOrbitsRep, IsPosInt],
function(poset,index)
    local cgr,nodeInfo,node;
    cgr:=poset!.colorGraphs[index];


    nodeInfo:=rec(names:=[],
                  values:=[],
                  testers:=[],
                  toStr:=[],
                  getters:=[],
                  maxlength:=0);
    

    node:=Objectify(NewType(CocoNodesFam, IsCocoNode and IsColorGraphNodeRep),
                   rec( poset:=poset,
                        index:=index,
                        level:=RankOfColorGraph(cgr),
                        cgr:=cgr,
                        nodeInfo:=nodeInfo));
    RegisterInfoCocoNode(node, rec(name:="Number:", value:=String(node!.index)));
    RegisterStandardInfo@(node);
    RegisterInfoCocoNode(node, rec(name:="algebraic:", value:=String(node!.index in node!.poset!.algebraicFusions)));
    return node;
end);


InstallMethod(NodeInfoString,
        "for coco nodes in ColorGraphNodeRep",
        [IsCocoNode and IsColorGraphNodeRep],
function(node)
    local str,res,ninf,maxlength,i,val;
    
        
    str:="";
    res:=OutputTextString( str, true );
    ninf:=node!.nodeInfo;
    maxlength:=Maximum(ninf.maxlength, 20);
    for i in [1..Length(ninf.names)] do
        if ninf.values[i]="unknown" and not ninf.names[i] in infoOptions@.disabled or node!.nodeInfo.testers[i](node) then
            val:=ninf.getters[i](node);
            if val <> fail then
                ninf.values[i]:=ninf.toStr[i](val);
            fi;
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
    local pos,val;
    
    pos:=Position(node!.nodeInfo.names,str);
    if pos=fail then
        return fail;
    fi;
    if node!.nodeInfo.values[pos]<>"unknown" then
        return;
    fi;
    if node!.nodeInfo.testers[pos](node) then
        val:=node!.nodeInfo.getters[pos](node);
        if val<>fail then
            node!.nodeInfo.values[pos]:=node!.nodeInfo.toStr[pos](val);
        fi;
    fi;
end);
