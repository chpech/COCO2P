StringCocoOrbReps@ := function(arg)
    local i,j,g,dom,str,res,orbs,l;

    res:="";
    str:=OutputTextString(res,true);
    SetPrintFormattingStatus(str,false);
    
    g:=arg[1];
    if Length(arg)=2 then
        dom:=arg[2];
    else
        dom:=[1..LargestMovedPoint(g)];
    fi;

    orbs:=Orbits(g,dom)-1;
    orbs:=List(orbs,Minimum);
    l:=0;
    for i in  orbs do
        PrintTo(str,"(",i,")");l:=l+2+Length(String(i));
        if i= orbs[Length(orbs)] then
            PrintTo(str,"\n");
        else
            PrintTo(str,"/");
            l:=l+1;
            if l>55 then
                PrintTo(str,"*\n");
                l:=0;
            fi;
        fi;
    od;
    CloseStream(str);
    return res;
end;

StringCocoPerm@:=function ( p )
    local  str,res,i,j,k,l;
    res:="";
    str:=OutputTextString(res,true);
    SetPrintFormattingStatus(str,false);

    i:=ShallowCopy(MovedPoints(p));
    l:=0;
    while not IsEmpty(i) do
        j:=RepresentativeSmallest(i);
        Unbind(i[Position(i,j)]);
        PrintTo(str,"(", j-1);
        l:=l+1+Length(String(j-1));
        k:=j^p;
        while k<>j do
            PrintTo(str,",", k-1);
            l:=l+1+Length(String(k-1));
            if(l>55) then PrintTo(str,"*\n"); l:=0; fi ;
            Unbind(i[Position(i,k)]);
            k:=k^p;
        od;
        PrintTo(str,")");
        l:=l+1;
        if(l>50) and not IsEmpty(i) then PrintTo(str,"*\n"); l:=0; fi ;
    od;
    CloseStream(str);

    return res;
end;


StringCocoGenerators@:=function(arg)
    local i,max,g,gens,str,res;

    res:="";
    str:=OutputTextString(res,true);
    SetPrintFormattingStatus(str,false);

    g:=arg[1];

    if g=Group(()) then return ""; fi;
    if Length(arg)=2 then
        max:=arg[2];
    else
        max:=LargestMovedPoint(g);
    fi;
    PrintTo(str,max, "\n");
    gens:=SmallGeneratingSet(g);
    PrintTo(str,Size(gens), "\n");
    for i in gens do
        PrintTo(str, StringCocoPerm@(i),"\n");
    od;
    CloseStream(str);
    return res;
end;

StringCocoMerging@:=function(mrg)
    local  res, str, l, cls, i;

    res:="";
    str:=OutputTextString(res,true);
    SetPrintFormattingStatus(str,false);
    
    l:=0;
    for cls in mrg-1 do
        PrintTo(str,"(");l:=l+1;
        for i in [1..Length(cls)-1] do
            PrintTo(str,cls[i],",");l:=l+1+Length(String(cls[i]));
            if l>55 then
                PrintTo(str,"*\n");
                l:=0;
            fi;
        od;
        PrintTo(str,cls[Length(cls)],")");
        l:=l+1+Length(String(cls[Length(cls)]));
        if l>50 and not cls = mrg[Length(mrg)] then
            PrintTo(str,"*\n");
            l:=0;
        fi;
    od;
    PrintTo(str,"\n");
    CloseStream(str);
    return res;
end;
