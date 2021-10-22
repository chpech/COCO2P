#############################################################################
##
##  tensor.gi                      COCO package
##                                                              Mikhail Klin
##                                                            Christian Pech
##                                                             Sven Reichard
##
##  Implementation for tensors
##
#############################################################################

TensorFam := NewFamily("TensorFam", IsTensor);


#################################################################
#R  IsTensorRep
##
DeclareRepresentation( "IsTensorRep", IsAttributeStoringRep,
        ["entries",
         "vertexNames",
         "knownAutGroup"
         ]);

##
#R  IsBlockedTensorRep
##
DeclareRepresentation( "IsBlockedTensorRep",
        IsAttributeStoringRep,
        ["reflexiveColors", # colors corresponding to fibres
         "rowBlk",          # for each color this stores the starting block $a$ of the color
                            # reflexiveColors[a] is the color of the fibre from which arc of color $i$
                            # start
         "colBlk",          # same like startBlk, just for the end of arcs
         "blocks",			# for blocks $a$ and $b$ blocks[a][b] contains the set of colors
                            # for which the start-block is $a$ and the end-block is $b$
         "blkIdx",          # for each color the index in its block
         "knownAutGroup",   #
         "vertexNames",     # names of the colors (that are vertices of the tensor...)
         "entries"          # the actual entries of the tensor
         ]);


############################################
#F  DenseTensorFromEntries( <entries> )
##    returns a tensor with the given group, order
##    and entries.
##   (entries[i][j][k] is the entry of the tensor at [i,j,k].
InstallGlobalFunction(DenseTensorFromEntries,
function(entries)
    local obj,ord;
    obj := rec();
    ord:=Length(entries);
    if ForAll(entries, x->Length(x)=ord and ForAll(x, y->Length(y)=ord)) then
       obj.entries:=entries;
       obj.knownAutGroup:=Group(());
       obj.vertexNames:=[1..ord];
       obj:= Objectify(NewType(TensorFam, IsTensorRep), obj);
       SetOrderOfTensor(obj,ord);
    else
       Error("Not a proper tensor!");
       return fail;
   fi;
   return obj;
end);



############################################
#F  TensorFromColorReps( <cgr>, <creps> )
##    Trys to construct a tensor of structure constants for <cgr>
##    <creps> is a list of arcs of <cgr>.
##    There has to be at least one arc from each color of <cgr>.
##    This constructor is not supposed to be used by the user of coco

InstallGlobalFunction(TensorFromColorReps,
function(cgr,tor)
   local o,r,k,i,j,tensor,mat,submat,
         row,column,pos,
         part,
         refl,irrefl,
         reflexiveColors, rowBlk, colBlk,
         blocks, blockIndices,
         entries,a,b,c,
         rb,cb,
         bltensor;

    part := List([1..RankOfColorGraph(cgr)], x->[]);
    refl:=List([1..RankOfColorGraph(cgr)], x->false);
    irrefl:=List([1..RankOfColorGraph(cgr)], x->false);
    for i in [1..Length(tor)] do
        j:=ArcColorOfColorGraph(cgr,tor[i]);
        Add(part[j], i);
        if tor[i][1]=tor[i][2] then
           refl[j]:=true;
        else
           irrefl[j]:=true;
        fi;
        if irrefl[j] and refl[j] then
           return fail;
        fi;
    od;

   reflexiveColors:=ListBlist([1..RankOfColorGraph(cgr)], refl);
   rowBlk:=[];
   colBlk:=[];
   blocks:=List([1..Length(reflexiveColors)], x->List([1..Length(reflexiveColors)], x->[]));
   blockIndices:=[];
   for i in [1..RankOfColorGraph(cgr)] do
      for o in part[i] do
          rb:=Position(reflexiveColors, ArcColorOfColorGraph(cgr, tor[o][1],tor[o][1]));
          if not IsBound(rowBlk[i]) then
             rowBlk[i]:=rb;
          else
             if rowBlk[i]<>rb then
               return fail;
             fi;
          fi;
          cb:=Position(reflexiveColors, ArcColorOfColorGraph(cgr, tor[o][2],tor[o][2]));
          if not IsBound(colBlk[i]) then
             colBlk[i]:=cb;
          else
             if colBlk[i]<>cb then
               return fail;
             fi;
          fi;
      od;
      Add(blocks[rowBlk[i]][colBlk[i]],i);
      blockIndices[i]:=Length(blocks[rowBlk[i]][colBlk[i]]);
   od;

   entries:=List([1..Length(reflexiveColors)],
            a->List([1..Length(reflexiveColors)],
               b->List([1..Length(reflexiveColors)],
                 c->[])));

   for r in tor do
      k:=ArcColorOfColorGraph(cgr,r);
      a:=rowBlk[k];
      b:=colBlk[k];
      mat:=LocalIntersectionArray(cgr,r);
      for c in [1..Length(reflexiveColors)] do
         submat:=List(mat{blocks[a][c]}, x->x{blocks[c][b]});
         if IsBound(entries[a][b][c][blockIndices[k]]) then
            if submat<>entries[a][b][c][blockIndices[k]] then
               return fail;
            fi;
         else
            entries[a][b][c][blockIndices[k]]:=submat;
         fi;
      od;
   od;

   if Length(blocks)>1 then
       for a in [1..Length(reflexiveColors)] do
           for b in [1..Length(reflexiveColors)] do
               for c in [1..Length(reflexiveColors)] do
                   bltensor:=[];
                   for k in [1..Length(entries[a][b][c])] do
                       for i in [1..Length(entries[a][b][c][k])] do
                           for j in [1..Length(entries[a][b][c][k][i])] do
                               if not IsBound(bltensor[i]) then
                                   bltensor[i]:=[];
                               fi;
                               if not IsBound(bltensor[i][j]) then
                                   bltensor[i][j]:=[];
                               fi;
                               bltensor[i][j][k]:=entries[a][b][c][k][i][j];
                           od;
                       od;
                   od;
                   entries[a][b][c]:=bltensor;
               od;
           od;
       od;
       tensor:=rec(
                   reflexiveColors := reflexiveColors,
                   rowBlk          := rowBlk,
                   colBlk          := colBlk,
                   blocks          := blocks,
                   blkIdx          := blockIndices,
                   knownAutGroup   := KnownGroupOfColorAutomorphisms(cgr),
                   vertexNames     := ColorNames(cgr),
                   entries         := entries
                   );

       tensor:=Objectify(NewType(TensorFam, IsBlockedTensorRep), tensor);
   else
       tensor := rec(
                     entries:=List([1..RankOfColorGraph(cgr)],i->
                             List([1..RankOfColorGraph(cgr)], j->
                                  List([1..RankOfColorGraph(cgr)],k->entries[1][1][1][k][i][j]))),
                     knownAutGroup   := KnownGroupOfColorAutomorphisms(cgr),
                     vertexNames     := ColorNames(cgr)
                     );

       tensor:= Objectify(NewType(TensorFam, IsTensorRep), tensor);
   fi;

   if HasMates(cgr) then
       SetMates(tensor, Mates(cgr));
   fi;
   SetReflexiveColors(tensor, reflexiveColors);
   SetOrderOfCocoObject(tensor, RankOfColorGraph(cgr));
   return tensor;
end
  )
  ;


#################################################################
#M  EntryOfTensor( <tensor>, <i>, <j>, <k> )
##   returns an entry of a tensor
##
InstallMethod(EntryOfTensor,
        "for dense tensors" ,
        [IsTensor and IsTensorRep,
         IsPosInt,
         IsPosInt,
         IsPosInt],
function(T, i,j,k)
    local result;
    return T!.entries[i][j][k];
end);

#################################################################
#M  EntryOfTensor( <tensor>, <i>, <j>, <k> )
##   returns an entry of a tensor
##
InstallMethod(EntryOfTensor,
     "for blocked tensors",
        [IsTensor and IsBlockedTensorRep,
         IsPosInt,
         IsPosInt,
         IsPosInt],
function(T,i,j,k)
    local a,b,c;
    a:=T!.rowBlk[i];
    if T!.rowBlk[k]<>a then
       return 0;
    fi;
    b:=T!.colBlk[j];
    if T!.colBlk[k]<>b then
       return 0;
    fi;
    c:=T!.colBlk[i];
    if T!.rowBlk[j]<>c then
       return 0;
    fi;
    return T!.entries[a][b][c][T!.blkIdx[i]][T!.blkIdx[j]][T!.blkIdx[k]];
end);

##################################################
#F  ComplexProduct
##################################################
InstallMethod(ComplexProduct,
    "for tensors",
    [IsTensor, IsList, IsList],
function(tensor, l1,l2)
    local i, j, k, product;
    product := ListWithIdenticalEntries(Order(tensor),0);
    for i in l1 do
        for j in l2 do
            for k in [1..Order(tensor)] do
                product[k] := product[k] + EntryOfTensor(tensor, i, j, k);
            od;
        od;
    od;
    return product;
end);

InstallMethod(ComplexProduct,
    "for tensors in representation TensorRep",
    [IsTensor and IsTensorRep, IsList, IsList],
function(tensor, set1,set2)
    local i, j, product;
    product := ListWithIdenticalEntries(Order(tensor),0);
    for i in set1 do
        for j in set2 do
            product := product + tensor!.entries[i][j];
        od;
    od;
    return product;
end);

InstallMethod( IsCommutativeTensor,
   "for tensors",
   [IsTensor],
function(tensor)
   local i, j, k;

   for i in [1..OrderOfCocoObject(tensor)] do
      for j in [i+1..OrderOfCocoObject(tensor)] do
         for k in [1..OrderOfCocoObject(tensor)] do
            if EntryOfTensor(tensor,i,j,k) <> EntryOfTensor(tensor,j,i,k) then
               return false;
            fi;
         od;
      od;
   od;
   return true;
end);

InstallMethod( IsCommutativeTensor,
   "for tensors",
   [IsTensor and HasAutGroupOfCocoObject],
function(tensor)
   local aaut,sor,r,i,j,k;
   aaut:=AutGroupOfCocoObject(tensor);
   if IsTrivial(aaut) then
      TryNextMethod();
   fi;
   sor:=CocoTwoSetOrbitRepresentatives(aaut,OrderOfCocoObject(tensor));
   for r in sor do
      i:=r[1]; j:=r[2];
      for k in [1..OrderOfCocoObject(tensor)] do
         if EntryOfTensor(tensor,i,j,k) <> EntryOfTensor(tensor,j,i,k) then
            return false;
         fi;
      od;
   od;
   return true;
end);



InstallMethod( IsCommutativeTensor,
        "for tensors",
        [IsTensor and IsTensorRep],
function(t)
    local   entries,  i,  j;
    entries := t!.entries;
    for i in [1..Order(t)] do
        for j in [i+1..Order(t)] do
            if entries[i][j] <> entries[j][i] then
                return false;
            fi;
        od;
    od;
    return true;
end);

InstallMethod( IsCommutativeTensor,
   "for tensors",
   [IsTensor and IsTensorRep and HasAutGroupOfCocoObject],
function(tensor)
   local aaut,entries,i,j,sor,r;

   aaut:=AutGroupOfCocoObject(tensor);
   entries:=tensor!.entries;
   if IsTrivial(aaut) then
      TryNextMethod();
   fi;
   sor:=CocoTwoSetOrbitRepresentatives(aaut,OrderOfCocoObject(tensor));
   for r in sor do
      i:=r[1]; j:=r[2];
      if entries[i][j] <> entries[j][i] then
         return false;
      fi;
   od;
   return true;
end);


InstallMethod(ReflexiveColors,
   "for tensors of coherent configurations",
   [IsTensor  and IsTensorOfCC],
function(tensor)
    local result;
    result := Filtered([1..Order( tensor )],
                      x -> EntryOfTensor( tensor, x, x, x ) = 1);
    result := Filtered(result, x -> Sum(ComplexProduct(tensor, [x], [x]))=1);
    return result;
end);


##################################################
#M Mates( <tensor> )
##
InstallMethod(Mates,
   "for tensors of coherent configurations",
   [IsTensor and IsTensorOfCC],
function(tensor)
    local reflexive, i, start, finish, mates, outvalencies,res;

    mates := [];
    outvalencies := [];
    reflexive := ReflexiveColors(tensor);
    for i in [1..Order(tensor)] do
        start := First(reflexive, x -> EntryOfTensor(tensor,x,i,i) = 1);
        finish := First(reflexive, x -> EntryOfTensor(tensor,i,x,i) = 1);
        mates[i] := First([1..Order(tensor)],
                          j -> EntryOfTensor(tensor,i,j,start) <> 0);
        outvalencies[i] := EntryOfTensor(tensor,i,mates[i],start);
    od;
    res:=PermList(mates);
    if res=fail then
        Error("???");
    fi;

    return res;
end);


InstallMethod(OutValencies,
   "for tensors of coherent configurations",
   [IsTensor and IsTensorOfCC],
function(tensor)
    local reflexive, i, start, finish, mates, outvalencies;

    mates := Mates(tensor);
    outvalencies := [];
    reflexive := ReflexiveColors(tensor);
    for i in [1..Order(tensor)] do
        start := First(reflexive, x -> EntryOfTensor(tensor,x,i,i) = 1);
        finish := First(reflexive, x -> EntryOfTensor(tensor,i,x,i) = 1);
        outvalencies[i] := EntryOfTensor(tensor,i,i^mates,start);
    od;
    return outvalencies;
end);

InstallMethod(FibreLengths,
   "for tensors of coherent configurations",
   [IsTensor and IsTensorOfCC],
function(tensor)
    local reflexive, i, pos, start,fiblens,outvalencies,fend;

    outvalencies := OutValencies(tensor);
    reflexive := ReflexiveColors(tensor);
    fiblens:=ListWithIdenticalEntries(Length(reflexive),0);
    for i in [1..Order(tensor)] do
        start := First(reflexive, x -> EntryOfTensor(tensor,x,i,i) = 1);
        fend  := First(reflexive, x -> EntryOfTensor(tensor,i,x,i) = 1);
        if start=fend then
            pos:=Position(reflexive,start);
            fiblens[pos]:=fiblens[pos]+outvalencies[i];
        fi;
    od;
    return fiblens;
end);

InstallMethod(StartBlock,
   "for tensors of coherent configurations",
   [IsTensor and IsTensorOfCC, IsPosInt],
function(tensor, i)
  local reflexive;
  reflexive:=ReflexiveColors(tensor);
  return PositionProperty(reflexive, x -> EntryOfTensor(tensor,x,i,i) = 1);
end);

InstallMethod(StartBlock,
   "for blocked tensors of coherent configurations",
   [IsTensor and IsTensorOfCC and IsBlockedTensorRep, IsPosInt],
function(tensor, i)
  return tensor!.rowBlk[i];
end);

InstallMethod(FinishBlock,
   "for tensors of coherent configurations",
   [IsTensor and IsTensorOfCC, IsPosInt],
function(tensor, i)
  local reflexive;
  reflexive:=ReflexiveColors(tensor);
  return PositionProperty(reflexive, x -> EntryOfTensor(tensor,i,x,i) = 1);
end);

InstallMethod(FinishBlock,
   "for tensors of coherent configurations",
   [IsTensor and IsTensorOfCC and IsBlockedTensorRep, IsPosInt],
function(tensor, i)
  return tensor!.colBlk[i];
end);

InstallMethod(BlockOfTensor,
   "for tensors of coherent configurations",
   [IsTensor and IsTensorOfCC, IsPosInt, IsPosInt],
function(tensor,row,col)
    local res;
    res:=Filtered([1..Order(tensor)], i->StartBlock(tensor,i) = row);
    return Filtered(res, i->FinishBlock(tensor,i)=col);
end);

InstallMethod(BlockOfTensor,
   "for tensors of homogeneous coherent configurations",
   [IsTensor and IsTensorOfCC and IsHomogeneousTensor, IsPosInt, IsPosInt],
function(tensor,row,col)
    
    if row>1 or col>1 then
        return [];
    else
        return [1..Order(tensor)];
    fi;
end);

InstallMethod(BlockOfTensor,
   "for blocked tensors of coherent configurations",
   [IsTensor and IsTensorOfCC and IsBlockedTensorRep, IsPosInt, IsPosInt],
function(tensor,row,col)
    local nof;
    nof:=Length(tensor!.reflexiveColors);
    
    if row >nof or col> nof then
        return [];
    else
        return ShallowCopy(tensor!.blocks[row][col]);
    fi;
end);


InstallMethod(KnownGroupOfAutomorphisms,
   "for dense tensors",
   [IsTensor and IsTensorRep],
function(tensor)
   return tensor!.knownAutGroup;
end);

InstallMethod(KnownGroupOfAutomorphisms,
   "for dense tensors",
   [IsTensor and IsBlockedTensorRep],
function(tensor)
   return tensor!.knownAutGroup;
end);

InstallGlobalFunction(NewPbagObjectForTensorOfCC,
function(tensor)
   local GlobalInvariant, InitialPartition, obj, G, initial, stab;

    GlobalInvariant:=function(T,i)
        local inv,blks,cand,part,refcol,start,finish,subdegs,fiblen;

        refcol:=ReflexiveColors(T);

        inv:=[];
        if i in refcol then
          Add(inv,0);
        else
          Add(inv,1);
        fi;

        if i^Mates(T)<>i then
          Add(inv,0);
        else
          Add(inv,1);
        fi;

        start := StartBlock(T,i);
        finish := FinishBlock(T,i);

        if start=finish then
          Add(inv,0);
        else
          Add(inv,1);
        fi;

        subdegs:=OutValencies(T);
        fiblen:=FibreLengths(T);
        Add(inv, fiblen[start]);
        Add(inv, fiblen[finish]);
        Add(inv, subdegs[i]);
        Add(inv, subdegs[i^Mates(T)]);

        return inv;
    end;
    InitialPartition:=function(T)
        local linvs,invs,part,ipart,i,j;

        linvs:=List([1..Order(T)], x->GlobalInvariant(T,x));
        invs:=Set(linvs);
        part:=List(invs, x->Filtered([1..Order(T)], y->linvs[y]=x));
        ipart:=[];
        for i in [1..Length(part)] do
          for j in part[i] do
            ipart[j]:=i;
          od;
        od;

        return [part,ipart];
    end;

    G:=KnownGroupOfAutomorphisms(tensor);

    initial:=InitialPartition(tensor);

    obj:=rec();
    obj.T:=tensor;
    obj.v:=Order(tensor);
    obj.fvc:=initial[2];
    obj.fcv:=initial[1];
    obj.ncp:=Length(obj.fcv);
    stab:=Filtered(initial[1], x->Length(x)=1);
    obj.ST:=List(stab, x->x[1]);
    obj.S:=[];
    obj.stabChain:=StabChainMutable(G);
    return obj;
end);

InstallMethod(NewPbagObject,
  "for tensors of coherent configurations",
  [IsTensor and IsTensorOfCC],
function(tensor)
  return NewPbagObjectForTensorOfCC(tensor);
end);

InstallMethod(NewPbagObjects,
   "for tensors of coherent configurations",
   [IsTensor and IsTensorOfCC, IsTensor and IsTensorOfCC],
function(tensor1,tensor2)
  return [NewPbagObjectForTensorOfCC(tensor1), NewPbagObjectForTensorOfCC(tensor2)];
end);

InstallGlobalFunction(NewPbagObjectForDenseTensor,
function(tensor)
   local  obj, G, initial, stab;

    G:=KnownGroupOfAutomorphisms(tensor);

    initial:=[[[1..Order(tensor)]], ListWithIdenticalEntries(Order(tensor),1)];

    obj:=rec();
    obj.T:=tensor;
    obj.v:=Order(tensor);
    obj.fvc:=initial[2];
    obj.fcv:=initial[1];
    obj.ncp:=Length(obj.fcv);
    stab:=Filtered(initial[1], x->Length(x)=1);
    obj.ST:=List(stab, x->x[1]);
    obj.S:=[];
    obj.stabChain:=StabChainMutable(G);
    return obj;
end);


InstallMethod(NewPbagObject,
  "for tensors",
  [IsTensor],
function(tensor)
  return NewPbagObjectForDenseTensor(tensor);
end);

InstallMethod(NewPbagObjects,
   "for tensors",
   [IsTensor, IsTensor],
function(tensor1,tensor2)
  return [NewPbagObjectForDenseTensor(tensor1), NewPbagObjectForDenseTensor(tensor2)];
end);


InstallMethod(PbagInvariant,
   "for tensors",
   [IsTensor, IsTensor],
function(tensor1,tensor2)
   local TestAutomorphism, TestIsomorphism, Invariant, HashFunction;

   TestIsomorphism:=function(T1, T2, perm)
       local W1,W2, i, j, k,o;

       W1:=T1.T;
       W2:=T2.T;
       o:=T1.v;
       for i in [1..o] do
          for j in [1..o] do
             for k in [1..o] do
                if EntryOfTensor(W1,i,j,k) <> EntryOfTensor(W2, i^perm, j^perm, k^perm) then
                                   return false;
                fi;
             od;
          od;
       od;
       return true;
   end;

   TestAutomorphism:=function(T1, perm)
       local W1,W2, i, j, k,o;

       W1:=T1.T;
       o:=T1.v;
       for i in [1..o] do
          for j in [1..o] do
             for k in [1..o] do
                if EntryOfTensor(W1,i,j,k) <> EntryOfTensor(W1, i^perm, j^perm, k^perm) then
                                   return false;
                fi;
             od;
          od;
       od;
       return true;
   end;

   Invariant:=function(TRec, i)
       local j, k, kidx, inv, inc, color1, color2,a,b,c,lk;
       inv:=[];

        for j in TRec.ST do
           Add(inv, EntryOfTensor(TRec.T, j,j,i));
           if TRec.S<>[] then
             lk:=[TRec.S[Length(TRec.S)]];
           else
             lk:=[];
           fi;
           for k in lk do #TRec.ST do
               Add(inv, EntryOfTensor(TRec.T,i,j,k));
               Add(inv, EntryOfTensor(TRec.T,i,k,j));
               Add(inv, EntryOfTensor(TRec.T,j,i,k));
               Add(inv, EntryOfTensor(TRec.T,j,k,i));
               Add(inv, EntryOfTensor(TRec.T,k,i,j));
               Add(inv, EntryOfTensor(TRec.T,k,j,i));
           od;
       od;
       Add(inv, TRec.fvc[i]);
       return inv;
   end;

   HashFunction:=function(Tinv)
       return Tinv*[1..Length(Tinv)];
   end;

   return rec(finv   :=Invariant,
              hashinv:=HashFunction,
              test   :=TestIsomorphism,
              autTest:=TestAutomorphism);
end);



InstallOtherMethod(NumberOfFibres,
		"for structure constants tensors",
		[IsTensor and IsTensorOfCC],
function(tensor)
   return Length(ReflexiveColors(tensor));
end);

InstallImmediateMethod(IsHomogeneousTensor,
		"for structure constants tensors",
	IsTensor and IsTensorOfCC,
function(tensor)
  return NumberOfFibres(tensor)=1;
end);

InstallOtherMethod(IsHomogeneous,
		"for structure constants tensors",
	[IsTensor and IsTensorOfCC],
function(tensor)
  return IsHomogeneousTensor(tensor);
end);


InstallMethod(VertexNamesOfCocoObject,
		"for tensors in TensorRep",
	[IsTensor and IsTensorRep],
function(tensor)
   return tensor!.vertexNames;
end);

InstallMethod(VertexNamesOfCocoObject,
		"for tensors in BlockedTensorRep",
	[IsTensor and IsBlockedTensorRep],
function(tensor)
   return tensor!.vertexNames;
end);


InstallMethod(PPolynomialOrdering, 
              "for structure constants tensors",
              [IsTensor and IsTensorOfCC, IsPosInt],
function(tensor,i)
    local  list, j, set, new;
    
    if not IsHomogeneousTensor(tensor) or not Mates(tensor)=() then
        return fail;
    fi;
    list:=[ReflexiveColors(tensor)[1],i];
    for j in [2..Order(tensor)-1] do
        set:=Filtered([1..Order(tensor)], k->EntryOfTensor(tensor,list[j],i,k)<>0);
        new:=Difference(set, Set([list[j-1],list[j]]));
        if Length(new)<>1 then
            return fail;
        fi;
        list[j+1]:=new[1];
    od;
    return list;
end);
    
InstallMethod(PPolynomialOrderings, 
              "for structure constants tensors",
              [IsTensor and IsTensorOfCC],
function(tensor)
    local  res;
    if not IsHomogeneousTensor(tensor) or not Mates(tensor)=() then
        return [];
    fi;
    res:=List(Difference([1..Order(tensor)], ReflexiveColors(tensor)), 
              i->PPolynomialOrdering(tensor,i));
    res:=Filtered(res, x->x<>fail);
    return res;
end);


InstallMethod(IsPPolynomial, 
              "for structure constants tensors",
              [IsTensor and IsTensorOfCC],
function(tensor)
    if not IsHomogeneousTensor(tensor) or not Mates(tensor)=() then
        return false;
    fi;
    
    return ForAny(Difference([1..Order(tensor)], ReflexiveColors(tensor)), i->PPolynomialOrdering(tensor,i)<>[]);
end);
         

InstallMethod(SetKnownGroupOfAutomorphismsNC,
		"for tensors in TensorRep",
     	[IsTensor and IsTensorRep, IsPermGroup],
function(tensor,g)

   tensor!.knownAutGroup:=g;
end);

InstallMethod(SetKnownGroupOfAutomorphismsNC,
		"for tensors in BlockedTensorRep",
     	[IsTensor and IsBlockedTensorRep, IsPermGroup],
function(tensor,g)

   tensor!.knownAutGroup:=g;
end);

InstallMethod(\=,
		"for tensors",
	[IsTensor, IsTensor],
function(tensor1,tensor2)
   local names1,names2,namemap,i,pos,j,k;

   if OrderOfTensor(tensor1)<>OrderOfTensor(tensor2) then
      return false;
   fi;

   names1:=VertexNamesOfCocoObject(tensor1);
   names2:=VertexNamesOfCocoObject(tensor2);
   namemap:=[];
   for i in [1..Length(names1)] do
      pos:=Position(names2,names1[i]);
      if pos=fail then
         return false;
      fi;
      namemap[i]:=pos;
   od;
   namemap:=PermList(namemap);
   for i in [1..OrderOfTensor(tensor1)] do
      for j in [1..OrderOfTensor(tensor1)] do
         for k in [1..OrderOfTensor(tensor1)] do
            if EntryOfTensor(tensor1,i,j,k)<> EntryOfTensor(tensor2, i^namemap,j^namemap,k^namemap) then
               return false;
            fi;
         od;
      od;
   od;
   return true;
end);

InstallMethod(FusionFamily,
	"for structure constants tensors",
	[IsTensor and IsTensorOfCC],
function(tensor)
   local fam;
   fam:=NewFamily("FusionFam", IsFusionOfTensor);
   return fam;
end);


InstallMethod(GoodSetsFamily,
    "for structure constants tensors",
	[IsTensor and IsTensorOfCC],
function(tensor)
   local fam;
   fam:=NewFamily("GoodSetsFam", IsGoodSet);
   return fam;
end);

InstallMethod(GoodSetOrbitFamilyOp,
        "for tensors and permutation groups",
        [IsTensor, IsPermGroup],
function(T,g)
    return NewFamily("GoodSetOrbitFam", IsGoodSetOrbit);
end);

InstallMethod(FusionOrbitFamilyOp,
        "for tensors and permutation groups",
        [IsTensor, IsPermGroup],
function(T,g)
    return NewFamily("FusionOrbitFam", IsFusionOrbit);
end);


InstallGlobalFunction( ClosureSet,
function( tensor, set )
    local result, oldset;
    result :=  Union(set, OnSets(set,Mates(tensor)));
    
    repeat
        oldset := result;
        result := ComplexProduct( tensor, oldset, oldset );
        result := Filtered([1..Length(result)], x -> result[x] <> 0);
        result := Union(result, oldset);
    until result = oldset;
    return result;
end);

##
InstallMethod( ClosedSets,
        "for tensors",
        [ IsTensor ],
        function( tensor )
    local   minimal,  sets,  i,  j,  new;

    minimal := List([1..Order(tensor)], x -> ClosureSet(tensor, [x]));
    sets := Set(minimal);
    for i in sets do
        for j in sets do
            new := ClosureSet( tensor, Union(i, j) );
            if not new in sets then
                Add(sets, new);
            fi;
        od;
    od;
    return sets;
end);

InstallOtherMethod( IsPrimitive,
        "for structure constants tensors",
        [IsTensor and IsTensorOfCC],
function(tensor)
    
    return IsHomogeneous(tensor) and ForAll(Difference([1..Order(tensor)],ReflexiveColors(tensor)), x->ClosureSet( tensor, [x] ) = [1..Order(tensor)]);
end);

InstallMethod( IsClosedSet,
               "for tensors and sets of colors",
               [IsTensor, IsList],
function(tensor,set)
    local prod,carrier;
    
    prod:=ComplexProduct(tensor,set,set);
    carrier:=Filtered([1..Length(prod)], x->prod[x]<>0);
    if carrier <> Set(set) then
        return false;
    fi;
    return true;
end);


InstallOtherMethod(\[\],
        "for tensors",
        [ IsTensor, IsList ],
        function( tensor, lidx)
    return EntryOfTensor(tensor,lidx[1],lidx[2],lidx[3]);
end);


#################################################################
#M  ViewString( <tensor> )
##
InstallMethod(ViewString,
        "for tensors",
        [IsTensor],
        function(x)
    local res;
    res:="<";
    if IsMutable(x) then
        Append(res, "mutable ");
    fi;
    res:=Concatenation(res, "Tensor of order ", String(Order(x)), ">");
    return res;
end);

#################################################################
#M  PrintString( <tensor> )
##
InstallMethod(PrintString,
        "for tensors",
        [IsTensor],
        function(x)
    return PRINT_STRINGIFY("DenseTensorFromEntries( ", x!.entries, " )");
end);

InstallMethod(String,
        "for tensors",
        [IsTensor],
        function(x)
    return STRINGIFY("DenseTensorFromEntries( ",
          KnownGroupOfAutomorphisms(x), ", ",
          Order(x), ", ", x!.entries,
          " )");
end);

##
TensorString := function(number,width)
    local i, l;

    if number=0 then
        return String("-", width);
    else
        return String(number,width);
    fi;
end;


##
InstallMethod( DisplayString,
        "for tensors",
        [IsTensor],
        function(x)
    local i, j, k, max, width, totalWidth,res;
    max := 0;
    for i in [1..Order(x)] do
        for k in [1..Order(x)] do
            for j in [1..Order(x)] do
                max := Maximum(max, Length(String(EntryOfTensor(x, i, j, k))));
            od;
        od;
    od;
    width := max+3;
    totalWidth := Order(x) * width + 1;
    res:=Concatenation("+", List([1..totalWidth], x -> '-'), "+\n");
    for i in [1..Order(x)] do
        for k in [1..Order(x)] do
            Append(res,"|");
            for j in [1..Order(x)] do
                Append(res, TensorString(EntryOfTensor(x, i, j, k), width));
            od;
            Append(res, " |\n");
        od;
        Append(res, Concatenation("+", List([1..totalWidth], x -> '-'), "+\n"));
    od;
    return res;
end);
