DeclareRepresentation("IsPartialSolutionRep",
        IsPartialSolution.
        [
         "k",
         "partSum",
         "partSolVector",
         "currIdx",
         "mset",
         "maxSummands",
         "maxRest",
         "gcds"
         ]);

# input: a matrix "mat", a vector "bound", a number "k"
# output: all vector x, such that 
#           x .mat = vec(k) 
# where vec(k) is the vecor whose every coordinate equals k,
# subject to the condition that 0<=x[i]<=bound[i], for all i.
AllSolutions:=function(mat,vec,bound,k)
    local nextPSol, isCompletePSol, emptyPSol;
    
    emptyPSol:=function(mat,vec,bound,k)
        local pSol,maxSummands,perm;
        
        pSol:=rec();
        
        pSol.maxSummands:=List([1..Length(mat)], i->bound[i]*mat[i]);
        perm:=[1..Length(pSol.maxSummands)];
        SortParallel(pSol.maxSummands, perm, function(a,b) return a>b;end);
        perm:=PermList(perm);
        pSol.mat:=Permuted(mat,perm);
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
                           x->Sum(maxSummands{[x..Length(maxSummands)]}));
        pSol.rest:=ListWithIdenticalEntries(Length(mat),k);
        pSol.k:=k;
        pSol.partSum:=List([1..Length(mat[1])], x->0);
        pSol.x:=ListWithIdenticalEntries(Length(mat),0);
        pSol.currIdx:=0;
        pSol.mi:=0;
        pSol.li:=0;
        return pSol;
    end;
    
    isCompletePSol:=function(pSol)
        if ForAny(pSol.partSum, x->x<>pSol.k) then
            return false;
        fi;
        return true;
    end;
    
        
