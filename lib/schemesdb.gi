InstallGlobalFunction(ReadG7File@,
function(name)
    local  path, ing7, s;
    
    path:=PackageInfo("coco2p")[1].InstallationPath;
    
    ing7:=InputTextFile(Concatenation(path,"as/",name,".g7.gz"));

    s:=ReadAll(ing7);
    CloseStream(ing7);

    s:=SplitString(s,"\n");
    s:=List(s, Chomp);
    return s;
end);

InstallGlobalFunction(MatrixFromCode@,
function(code)
    local  n, mat;
    
    n:=Sqrt(Length(code));
    if not IsInt(n) then
        ErrorNoReturn("MatrixFromCode: Length of code must be a square.");
    fi;
    mat:=List([0..n-1],i->code{[i*n+1..i*n+n]});
    mat:=List(mat, x->List(x, y->IntChar(y)-33));
    return mat;
end);

InstallGlobalFunction(CodeFromMatrix@,
function(mat)
    local  code;
    
    code:=Concatenation(mat+33);
    
    Apply(code,CharInt);
    return code;
end);

InstallGlobalFunction(AllAssociationSchemes,
function(n)
    local  orders, suff, nameshort, lcode, lmat, res;
    
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
    lcode:=ReadG7File@(nameshort);
    lmat:=List(lcode, MatrixFromCode@);
    
    res:= List(lmat, ColorGraphByMatrix);
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
        Info(InfoCOCO,1, Concatenation("AllCoherentConfigurations: Only degrees ", String(orders)," are available.\n"));
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
