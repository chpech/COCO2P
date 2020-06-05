# input: a matrix "mat", a vector "bound", a number "k"
# output: all vector x, such that 
#           x .mat = vec(k) 
# where vec(k) is the vecor whose every coordinate is equals to k,
# subject to the condition that 0<=x[i]<=bound[i], for all i.
MAX_SOLUTIONS@:=-1;

InstallGlobalFunction(BoundedSolutionsOfSLDE,
function(mat,bound,k)
    local nextPSol, isCompletePSol, emptyPSol,updatePSol,
          aVeryBigNumber,recursion,solutions,pSol,perm;
    
    aVeryBigNumber:=100000;

    emptyPSol:=function(mat,bound,k)
        local pSol,perm,i,j;
        
        pSol:=rec();
        
        pSol.maxSummands:=List([1..Length(mat)], i->bound[i]*mat[i]);
        perm:=[1..Length(pSol.maxSummands)];
        SortParallel(pSol.maxSummands, perm, function(a,b) return a>b;end);
        perm:=PermList(perm)^-1;
        pSol.mat:=Permuted(mat,perm);
        pSol.bound:=Permuted(bound,perm);
        Assert(1,pSol.maxSummands = List([1..Length(pSol.mat)], i->pSol.bound[i]*pSol.mat[i]));
        
        pSol.perm:=perm;
        pSol.gcds:=List([1..Length(pSol.mat)],
                   x->List([1..Length(pSol.mat[x])], 
                           z->Gcd(List([x..Length(pSol.mat)], 
                                   y->pSol.mat[y][z]))));
        # gcds[x][z]=Gcd { mat[y][z] | y in {x,...,|mat|} } .
        for i in pSol.gcds do
            for j in [1..Length(i)] do
                if i[j]=0 then
                    i[j]:=1;
                fi;
            od;
        od;
        pSol.maxRest:=List([1..Length(pSol.maxSummands)],
                           x->Sum(pSol.maxSummands{[x..Length(pSol.maxSummands)]}));
        #pSol.rest:=ListWithIdenticalEntries(Length(mat),k);
        pSol.k:=k;
        pSol.partSum:=List([1..Length(mat[1])], x->0);
        pSol.x:=ListWithIdenticalEntries(Length(mat),0);
        
        return pSol;
    end;
    
    updatePSol:=function(pSol,currIdx,i)
        pSol.partSum:=pSol.partSum+pSol.mat[currIdx]*(i-pSol.x[currIdx]);
        pSol.x[currIdx]:=i;
    end;
    
    
    isCompletePSol:=function(pSol)
        if ForAny(pSol.partSum, x->x<>pSol.k) then
            return false;
        fi;
        return true;
    end;
    
    recursion:=function(psol,currIdx)
        local li,mi,i,j,rest;
        
        
        if MAX_SOLUTIONS@>=0 and Length(solutions)>MAX_SOLUTIONS@ then
          return;
        fi;
        COCOPrint(pSol.x,"\n");
        
        if isCompletePSol(pSol) then 
            Add(solutions, ShallowCopy(pSol.x));
            
            if Length(solutions) mod 1000 =0 then
               Info(InfoSLDE,2,Length(solutions));
            fi;
            return;
        fi;
        
        if currIdx>Length(pSol.mat) then
            return;
        fi;
        
        rest:=List(pSol.partSum, x->k-x);
        
        if ForAny([1..Length(rest)], x->rest[x] > pSol.maxRest[currIdx][x]) then
            return;
        fi;
        
        if ForAny([1..Length(rest)], x->RemInt(rest[x], pSol.gcds[currIdx][x])<>0) then
            return;
        fi;
        
        
        mi:=aVeryBigNumber;
        for i in [1..Length(rest)] do
            if pSol.mat[currIdx][i]<>0 then
                j:=QuoInt(rest[i],pSol.mat[currIdx][i]);
                if j <mi then
                    mi:=j;
                fi;
            fi;
        od;
        
        mi:=Minimum(pSol.bound[currIdx],mi);
        
        if currIdx=Length(pSol.mat) then
            updatePSol(pSol,currIdx,mi);
            recursion(pSol,currIdx+1);
            updatePSol(pSol,currIdx,0);
            return;
        fi;
        
        li:=0;
        for i in [1..Length(rest)] do
            if rest[i]-pSol.maxRest[currIdx+1][i]>0 then
                if pSol.mat[currIdx][i]<>0 then
                    j:=QuoInt(rest[i]-pSol.maxRest[currIdx+1][i],pSol.mat[currIdx][i]);
                    if j>li then
                        li:=j;
                    fi;
                fi;
            fi;
        od;
        
        
        for i in [mi,mi-1..li] do
            updatePSol(pSol,currIdx,i);
            recursion(pSol,currIdx+1);
        od;
        
        updatePSol(pSol,currIdx,0);
        return;
    end;
    
    solutions:=[];
    
    pSol:=emptyPSol(mat,bound,k);
    
    perm:=pSol.perm^(-1);
    recursion(pSol,1);
    return List(solutions, sol->Permuted(sol, perm));
end);

