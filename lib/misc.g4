MakeDoc@:=function()
    local  cp, info, path;
    
    cp:=Filename(DirectoryCurrent(),"");
    info:=PackageInfo("coco2p");
    if info = [] then
        ErrorNoReturn("MakeDoc@COCO2P: Can not find the package directory of COCO2P!");
    fi;
    info:=info[1];
    path:=info.InstallationPath;
    if not ChangeDirectoryCurrent(path) then
        ErrorNoReturn("MakeDoc@COCO2P: Can not change to package directory!");
    fi;
    Read("makedoc.g");
    if not ChangeDirectoryCurrent(cp) then
        ErrorNoReturn("MakeDoc@COCO2P: Can not reset current path!");
    fi;
end;

StringCocoOrbReps@ := function(arg)
    local i,j,g,dom,str,res,orbs,l,s;

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
#    orbs:=List(orbs,Minimum);
    l:=0;
    for i in  orbs do
        s:=Concatenation("(",String(Minimum(i)),")");
        Append(s,String(Length(i)));
        PrintTo(str,s);l:=Length(s);
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

StringCocoMerging@:=function(gmrg)
    local  res, str, l, cls, i, mrg;

    res:="";
    str:=OutputTextString(res,true);
    SetPrintFormattingStatus(str,false);
    
    mrg:=gmrg-1;
    
    l:=0;
    for cls in mrg do
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

StringCocoList@:=function(s)
    local str,res,i;
    res:="";
    str:=OutputTextString(res,true);
    SetPrintFormattingStatus(str,false);

    for i in [1..Length(s)] do
        PrintTo(str,s[i]);
        if i<Length(s) then
            PrintTo(str,",");
        fi;
    od;
    CloseStream(str);
    return res;
end;


TodayString@:=function()
    local  path, date, stdin, res, str, dir,v;
    path:=DirectoriesSystemPrograms();;
    date:=Filename(path,"date");
    if date = fail then
        return "unknown";
    fi;
    
    stdin := InputTextUser();
    res:="";
    str:=OutputTextString(res,true);
    SetPrintFormattingStatus(str,false);
    dir:=DirectoryCurrent( );
    v:=Process(dir, date, stdin,str, ["+\%Y-\%m-\%d"]);
    CloseStream(str);
    if v <> 0 then
        return "unknown";
    fi;

    return Chomp(res);
end;

COCORotorMod:=10000;
