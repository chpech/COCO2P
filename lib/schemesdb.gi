InstallGlobalFunction(AllAssociationSchemes,
function(n)
    local   orders,  suff,  name, nameshort,res,tempvar,fnameshortreadonly;
    
    orders:=Difference([1..40],[1,2,35,36,37,39,40]);
    
    if not n in orders then
        Info(InfoCOCO,1, Concatenation("AllAssociationSchemes: Only degrees ", orders," are availably."));
        return fail;
    fi;
    if n in [0..9] then 
        suff:=Concatenation("0",String(n));
    else
        suff:=String(n);
    fi;
    
    nameshort:=Concatenation("as",suff);
    name:=Concatenation(nameshort,"@COCO2P");
    
    
    if not IsBoundGlobal(name) then
        if IsBoundGlobal(nameshort) then
            fnameshortreadonly:=IsReadOnlyGlobal(nameshort);
            tempvar:=ValueGlobal(nameshort);
            UnbindGlobal(nameshort);
            ReadWeb(Concatenation("http://math.shinshu-u.ac.jp/~hanaki/as/data/as", suff));
            BindGlobal(name, ValueGlobal(nameshort));
            UnbindGlobal(nameshort);
            BindGlobal(nameshort, tempvar);
            if not fnameshortreadonly then
                MakeReadWriteGlobal(nameshort);
            fi;
        else
            ReadWeb(Concatenation("http://math.shinshu-u.ac.jp/~hanaki/as/data/as", suff));
            BindGlobal(name, ValueGlobal(nameshort));
            UnbindGlobal(nameshort);
        fi;
#        MakeReadOnlyGlobal(name);
    fi;
    
    res:= List(ValueGlobal(name), ColorGraphByMatrix);
    Perform(res, function(x) SetIsWLStableColorGraph(x,true); end);
    Perform(res, function(x) SetIsHomogeneous(x,true); end);
    Perform([1..Length(res)], function(i) SetName(res[i], Concatenation("AS(", String(n),",", String(i),")")); end);
    return res;
    
end);

InstallGlobalFunction(AllCoherentConfigurations,
function(n)
    local   f,orders,  suff,  name, nameshort,res,tempvar,fnameshortreadonly;
    
    orders:=[1..15];
    
    if not n in orders then
        Info(InfoCOCO,1, Concatenation("AllCoherentConfigurations: Only degrees ", orders," are availably."));
        return fail;
    fi;
    if n in [0..9] then 
        suff:=Concatenation("0",String(n));
    else
        suff:=String(n);
    fi;
    
    nameshort:=Concatenation("cc",suff);
    name:=Concatenation(nameshort,"@COCO2P");
    
    
    if not IsBoundGlobal("cclist@COCO2P") then
        f := SingleHTTPRequest( "my.svgalib.org", 80, "GET", "/math-data/ccs1_15n", rec( ), false, false );
        if f.statuscode = 404  then
            UnbindGlobal("cclist@COCO2P");
            ErrorNoReturn( "File not found -- Check URL" );
        elif f.statuscode >= 400  then
            UnbindGlobal("cclist@COCO2P");
            ErrorNoReturn( "HTTP error code ", f.statuscode );
        fi;
        f:=f.body;
        f:=Concatenation("cclist@COCO2P:=",f,";");
        Read( InputTextString( f ) );
        MakeReadOnlyGlobal("cclist@COCO2P");
    fi;
    res:= List(ValueGlobal("cclist@COCO2P")[n], ColorGraphByMatrix);
    Perform(res, function(x) SetIsWLStableColorGraph(x,true); end);
    Perform([1..Length(res)], function(i) SetName(res[i], Concatenation("CC(", String(n),",", String(i),")")); end);
    return res;
    
end);
