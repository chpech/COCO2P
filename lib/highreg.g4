# this reads the contents of the variable GRAPHTYPESCACHE@COCO2P
ReadPackage("coco2p", "lib/graphtypes.g");


OnePointExtensions@:=function(gamma,theta,prt)
    local  l, nbg, cand, i, nbgi, nnbgi;
    if Length(prt)=OrderGraph(theta) then
        return fail;
    fi;
    l:=Length(prt)+1;
    nbg:=Adjacency(theta,l);
    cand:=[1..OrderGraph(gamma)];
    for i in [1..Length(prt)] do
        nbgi:=Adjacency(gamma,prt[i]);
        nnbgi:=Difference([1..OrderGraph(gamma)], nbgi);
        RemoveSet(nnbgi,prt[i]);
        if i in nbg then
            cand:=Intersection(cand, nbgi);
        else
            cand:=Intersection(cand,nnbgi);
        fi;
    od;
    cand:=Difference(cand, Set(prt));
    return cand;
end;



CountExtensionsSym@:=function(gamma,theta,prt)
    local  recure,h;


    recure:=function(h,prt)
        local lres,lv,orbs,orbreps,i,newh,newprt;

        lres:=0;

        lv:=OnePointExtensions@(gamma,theta,prt);

        if Length(prt)+1=OrderGraph(theta) then
            return Length(lv);
        fi;
        orbs:=Orbits(h,lv);
        orbreps:=List(orbs,Representative);

        for  i in [1..Length(orbreps)]  do
            newh:=Stabilizer(h,orbreps[i]);
            newprt:=Concatenation(prt,[orbreps[i]]);



            lres:=lres+Index(h, newh)*recure(newh,newprt);
        od;
        return lres;
    end;

    if IsBound(gamma.autGroup) then
        h:=gamma.autGroup;
    else
        h:=gamma.group;
    fi;

    if prt<>[] then
        h:=Stabilizer(h,prt,OnTuples);
    fi;

    return recure(h,prt);
end;

TOrbitRepresentatives@:=function(g,dom,t)
    local recure,res;

    res:=[];

    recure:=function(g,dom,t,rep)
        local o,v;

        if Length(rep)=t then
            Add(res, rep);
            return;
        fi;

        o:=List(OrbitsDomain(g,dom), Representative);
        for v in o do
            recure(Stabilizer(g,v),Difference(dom,[v]),t,Concatenation(rep,[v]));
        od;
    end;

    recure(g,dom,t,[]);

    return res;
end;

TypeOfTuple@:=function(gamma,t)
    local  s;

    s:=Set(t);
    return List([1..Length(t)], i->Set(Intersection(Adjacency(gamma,t[i]), s), v->Position(t,v)));
end;


IsRegularForType@:=function(gamma,theta)
    local  reps, lreps, r, i,lcnt,tp,n,g,h;

    if IsBound(gamma.autGroup) then
        g:=gamma.autGroup;
    else
        g:=gamma.group;
    fi;

    reps:=TOrbitRepresentatives@(g,[1..OrderGraph(gamma)],theta.base);

    lreps:=[];
    lcnt:=[];

    for r in reps do
        n:=CountExtensionsSym@(gamma,theta,r);
        tp:=TypeOfTuple@(gamma,r);
        i:=Position(lreps,tp);

        if i = fail then
            Add(lreps,tp);
            i:=Length(lreps);
            Add(lcnt,n);
            continue;
        fi;
        if n <> lcnt[i] then
            return false;
        fi;
    od;
    return [lreps,lcnt];
end;

# restriction on the arguments: 1<=n<=4, n<m, 2<=m<=7 
# it returns true if in addition gamma is (n,m)-regular
IsHighlyRegularGraph:=function(gamma,n,m)
    local ltp,params,c,tp;
    
    
    if not n in [1..4] then
        ErrorNoReturn("IsHighlyRegularGraph(gamma,n,m) is implemented only for 1 <= n <= 4.");
    fi;
    if not m in [2..7] then
        ErrorNoReturn("IsHighlyRegularGraph(gamma,n,m) is implemented only for 1 <= m <= 7.");
    fi;
    if m<n then
        return fail;
    fi;
    
    if not IsBound(gamma.highlyregular) then
        gamma.highlyregular:=[];
    fi;
    if not IsBound(gamma.highlyregular[n]) then
        gamma.highlyregular[n]:=[];
    fi;
    if IsBound(gamma.highlyregular[n][m]) then
        return gamma.highlyregular[n][m]<>false;
    fi;
    
        
    if n=1 and m=2 then
        return IsRegularGraph(gamma);
    fi;
    
    if m>n+1 and not IsHighlyRegularGraph(gamma,n,m-1) then
        gamma.highlyregular[n][m]:=false;
        return false;
    elif n>1 and not IsHighlyRegularGraph(gamma,n-1,n) then
        gamma.highlyregular[n][m]:=false;
        return false;
    fi;
    
    ltp:=GRAPHTYPESCACHE@COCO2P[n+1][m+1][n+2];
    params:=[];
    for tp in ltp do
        c:=IsRegularForType@(gamma,tp);
        if c=false then
            gamma.highlyregular[n][m]:=false;
            return false;
        fi;
        Add(params,c);
    od;
    
    gamma.highlyregular[n][m]:=params;
    return true;
end;
