# strongly regular graphs

# triangular graphs

Multiset := function (z)
    return  List(Set(z), x ->[x,Length(Filtered(z, y -> y=x))]);
end;

IsStronglyRegular := function(gamma)
    local parameters, diameter, delta;
    
    if not IsGraph(gamma)  then
        Error(" usage: IsStronglyRegular( <Graph> ) ");
        return false;
    fi;
              
    if "isStronglyRegular" in RecFields(gamma) then
        return gamma.isStronglyRegular;
    fi;
    if not IsSimpleGraph(gamma) then    #contains loops
        gamma.isStronglyRegular := false;
        return false;
    fi;
    if not IsDistanceRegular(gamma) then
        gamma.isStronglyRegular := false;
        return false;
    fi;
    diameter := Diameter(gamma);
    if diameter = 2 then
        gamma.isStronglyRegular := true;
        gamma.srg := rec();
        parameters := GlobalParameters(gamma);
        gamma.srg.v := gamma.order;
        gamma.srg.k := parameters[1][3];
        gamma.srg.lambda := parameters[2][2];
        gamma.srg.mu := parameters[3][1];
        delta := RootInt((gamma.srg.lambda-gamma.srg.mu)^2 + 
                         4*(gamma.srg.k-gamma.srg.mu));
        gamma.srg.r := (gamma.srg.lambda-gamma.srg.mu + delta)/2;
        gamma.srg.s := (gamma.srg.lambda-gamma.srg.mu - delta)/2;
    else
        gamma.isStronglyRegular := false;
    fi;
    return gamma.isStronglyRegular;
end;

Switch := function (gamma, s) #Seidel switch w.r.t. vertex subset s
    local f;
    f := function (x,y)
        if x in s and y in s then
            return x in Adjacency(gamma,y);
        fi;
        if not (x in s) and not (y in s) then
            return x in Adjacency(gamma,y);
        fi;
        return not (x in Adjacency(gamma,y));
    end;
    return Graph(Group(()), Vertices(gamma), OnPoints, f);
end;


SubConstituent := function(arg)
    local gamma,gamma1,point;
    if Length(arg) = 2 then
        point := arg[2];
    else
        point := 1;
    fi;
    gamma := arg[1];
    gamma1 := InducedSubgraph(gamma,
                      Adjacency(gamma,point),
                      Stabilizer(gamma.group,point, OnPoints));
    if IsBound(gamma.name) then
        gamma1.name := Concatenation("Sub(", 
                               gamma.name, ",", 
                               String(point),")");
    fi;
    return gamma1;
end;
CosubConstituent := function(arg)
    local gamma,gamma1,point;
    if Length(arg) = 2 then
        point := arg[2];
    else
        point := 1;
    fi;
    gamma := arg[1];
    gamma1 := InducedSubgraph(gamma,
                      Difference([1..gamma.order],
                              Union(Adjacency(gamma,point),[point])),
                      Stabilizer(gamma.group,point, OnPoints));
    if IsBound(gamma.name) then
        gamma1.name := Concatenation("Cosub(", 
                               gamma.name, ",", 
                               String(point),")");
    fi;
    return gamma1;
end;

                    


IsoClassReps := function(graphList)
    local representatives,new,gamma,rep;
    representatives := [];
    for gamma in graphList do
        new := true;
        for rep in representatives do
            if IsIsomorphicGraph(gamma,rep) then
               new := false;
            fi;
        od;
        if new then
            Add(representatives,gamma);
        fi;
    od;
    return representatives;
end;

IsPseudoGeometric := function(gamma)
    
    local K, R, T;    

    if not IsStronglyRegular(gamma) then
        Print("no srg\n");
        return  false;
    fi;
    
    if "isPseudoGeometric" in RecFields(gamma) then
    #    Print("already in record\n");
        return gamma.isPseudoGeometric;
    fi;
    
    R := -gamma.srg.s;
    
    T := gamma.srg.mu / R;
    if not IsInt(T) then
    #    Print("T = ", T, "no integer\n");
        gamma.isPseudoGeometric := false;
        return false;
    fi;
    
    K := gamma.srg.r + T + 1;
    if gamma.order = K*(1+(K-1)*(R-1)/T) and
       gamma.srg.k = R*(K-1) and
       gamma.srg.lambda = (K-2) + (R-1)*(T-1) and
       T <= K and T <= R then
        gamma.isPseudoGeometric := true;
        gamma.psg := rec(K := K, R := R, T := T);
        return true;
    else
        gamma.isPseudoGeometric := false;
        return false;
    fi;
    
end;


SRG_IN := [];
SRG_Index := [];
SRG_DIR := "/Users/pech/Documents/My Programs/srg.database/";
SRGfilename := function(gamma)
    local srg;
    srg := gamma.srg;
    return Concatenation(String(gamma.order), ".",
                   String(srg.k), ".",
                   String(srg.lambda), ".",
                   String(srg.mu));
end;

AddToDatabase := function(arg)
    local srg, i,gamma, name;
    gamma := arg[1];
    SetAutGroupCanonicalLabelling(gamma);
    gamma := NewGroupGraph(AutGroupGraph(gamma), gamma);
    if not IsStronglyRegular(gamma) then
        Print("not strongly regular\n");
        return;
    fi;
    if gamma.srg.k * 2 > gamma.srg.v-1 then
        gamma := ComplementGraph(gamma);
        if not IsStronglyRegular(gamma) then
            Print("not a primitive srg");
            return;
        fi;
    fi;
    if Length(arg) >1 then
        gamma.discovery := arg[2];
    fi;
    srg := gamma.srg;
    
    Read(Concatenation(SRG_DIR, "Index"));
    if not [srg.v, srg.k, srg.lambda, srg.mu] in SRG_Index then
        Print("New parameter set!\n");
        PrintTo(Concatenation(SRG_DIR, SRGfilename(gamma)),
                "SRG_IN := [\n", gamma, "\n];\n");
        AddSet(SRG_Index, [srg.v, srg.k, srg.lambda, srg.mu]);
        PrintTo(Concatenation(SRG_DIR, "Index"), 
                "SRG_Index :=\n", SRG_Index, ";\n");
        
        return;
    fi;
    Read(Concatenation(SRG_DIR, SRGfilename(gamma)));
    for i in SRG_IN do
        if IsIsomorphicGraph(gamma, i) then
            Print("Already in database");
            if IsBound(i.discovery) then
                Print(" ( ", i.discovery, " )\n");
                return;
            elif IsBound(gamma.discovery)  then
                i.discovery := gamma.discovery;
                PrintTo(Concatenation(SRG_DIR, SRGfilename(gamma)), 
                        "SRG_IN := \n", SRG_IN, ";\n");
                Print(" added note ", gamma.discovery,"\n");
                return;
            else
                Print("\n");
                return;
            fi;
        fi;
    od;
    Add(SRG_IN, gamma);
    Print("New graph added to ", SRGfilename(gamma), 
          "; graph # ", Length(SRG_IN), "\n");
    PrintTo(Concatenation(SRG_DIR, SRGfilename(gamma)), 
            "SRG_IN := \n", SRG_IN, ";\n");
    return;
end;

RetrieveFromDatabase := function(f)
    local list, i;
    list := [];
    Read(Concatenation(SRG_DIR, "Index"));
    SRG_Index := Filtered(SRG_Index, x -> f(x[1], x[2], x[3], x[4]));
    for i in SRG_Index do 
        Print(i, ": ");
        Read(Concatenation(SRG_DIR, String(i[1]), ".",
                String(i[2]), ".", 
                String(i[3]), ".", String(i[4])));
        Print(Length(SRG_IN), " graphs found;\n");
        list := Concatenation(list, SRG_IN);
    od;
    Print(Length(list), " graphs altogether.\n");
    return list;
end;

IndexDatabase := function()
    local list, i;
    list := [];
    Read(Concatenation(SRG_DIR, "Index"));
    return SRG_Index;
end;
