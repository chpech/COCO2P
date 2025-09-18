InstallGlobalFunction(ReadG7File@,
function(name)
    local  path, ing7, s;
    
    
    ing7:=InputTextFile(name);

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
    if Maximum(code) > 95 then
        ErrorNoReturn("CodeFromMatrix@COCO2P(matrix): the maximal entry of matrix should be <= 95");
    fi;
    
    Apply(code,CharInt);
    return code;
end);

InstallGlobalFunction(AllAssociationSchemes,
function(n)
    local  suff, nameshort, path, name, lcode, lmat, res;
    
    
    if not SmallAssociationSchemesAvailable(n) then
        Info(InfoCOCO,1, Concatenation("AllAssociationSchemes: Only degrees ",
                 StringCocoList@(SmallAssociationSchemesAvailable())," are availably."));
        return fail;
    fi;
    if n in [0..9] then 
        suff:=Concatenation("0",String(n));
    else
        suff:=String(n);
    fi;
    
    nameshort:=Concatenation("as",suff);
    path:=PackageInfo("coco2p")[1].InstallationPath;
    name:=Concatenation(path,"as/",nameshort,".g7.gz");

    lcode:=ReadG7File@(name);
    lmat:=List(lcode, MatrixFromCode@);
    
    res:= List(lmat, ColorGraphByMatrix);
    Perform(res, function(x) SetIsWLStableColorGraph(x,true); end);
    Perform(res, function(x) SetIsHomogeneous(x,true); end);
    Perform([1..Length(res)], function(i) SetName(res[i], Concatenation("AS(", String(n),",", String(i),")")); end);
    return res;    
end);


InstallGlobalFunction(SmallAssociationScheme,
function(n,i)
    local  suff, nameshort, path, name, lcode, mat, cgr;
    
    if not SmallAssociationSchemesAvailable(n) then
        Info(InfoCOCO,1, Concatenation("SmallAssociationScheme: Only degrees ", 
                                       StringCocoList@(SmallAssociationSchemesAvailable())," are availably."));
        return fail;
    fi;
    if n in [0..9] then 
        suff:=Concatenation("0",String(n));
    else
        suff:=String(n);
    fi;
    
    nameshort:=Concatenation("as",suff);
    path:=PackageInfo("coco2p")[1].InstallationPath;
    name:=Concatenation(path,"as/",nameshort,".g7.gz");
    lcode:=ReadG7File@(name);
    if i > Length(lcode) then
        Info(InfoCOCO,1,Concatenation("SmallAssociationScheme: There are only ", String(Length(lcode))," association schemes of degree ", String(n),"."));
        return fail;
    fi;
    
    mat:=MatrixFromCode@(lcode[i]);
    cgr:=ColorGraphByMatrix(mat);
    SetIsWLStableColorGraph(cgr,true);
    SetIsHomogeneous(cgr,true);
    SetName(cgr, Concatenation("AS(", String(n),",", String(i),")"));
    return cgr;
end);

InstallGlobalFunction(NumberAssociationSchemes,
function(n)
    local  suff, nameshort, path, name, lcode;
    
    if not SmallAssociationSchemesAvailable(n) then 
        Info(InfoCOCO,1, Concatenation("NumberAssociationSchemes: Only degrees ", 
                                       StringCocoList@(SmallAssociationSchemesAvailable())," are availably."));
        return fail;
    fi;
    if n in [0..9] then 
        suff:=Concatenation("0",String(n));
    else
        suff:=String(n);
    fi;
    
    nameshort:=Concatenation("as",suff);
    path:=PackageInfo("coco2p")[1].InstallationPath;
    name:=Concatenation(path,"as/",nameshort,".g7.gz");
    lcode:=ReadG7File@(name);
    return Length(lcode);
end);


InstallGlobalFunction(SmallAssociationSchemesAvailable,
function(arg)
    
    if arg=[] then
        return smallAssociationSchemesAvailable@;
    fi;
    return arg[1] in smallAssociationSchemesAvailable@;
end);


InstallGlobalFunction(AllCoherentConfigurations,
function(n)
    local  suff, nameshort, path, name, lcode, lmat, res;
    
    
    if not SmallCoherentConfigurationsAvailable(n) then
        Info(InfoCOCO,1, Concatenation("AllCoherentConfigurations: Only degrees ",
                 StringCocoList@(SmallCoherentConfigurationsAvailable())," are availably."));
        return fail;
    fi;
    if n in [0..9] then 
        suff:=Concatenation("0",String(n));
    else
        suff:=String(n);
    fi;
    
    nameshort:=Concatenation("cc",suff);
    path:=PackageInfo("coco2p")[1].InstallationPath;
    name:=Concatenation(path,"cc/",nameshort,".g7.gz");
    lcode:=ReadG7File@(name);
    lmat:=List(lcode, MatrixFromCode@);
    
    res:= List(lmat, ColorGraphByMatrix);
    Perform(res, function(x) SetIsWLStableColorGraph(x,true); end);
    Perform([1..Length(res)], function(i) SetName(res[i], Concatenation("CC(", String(n),",", String(i),")")); end);
    return res;    
end);
    
InstallGlobalFunction(NumberCoherentConfigurations,
function(n)
    local  suff, nameshort, path, name, lcode;
    
    if not SmallCoherentConfigurationsAvailable(n) then 
        Info(InfoCOCO,1, Concatenation("NumberCoherentConfigurations: Only degrees ", 
                                       StringCocoList@(SmallCoherentConfigurationsAvailable())," are availably."));
        return fail;
    fi;
    if n in [0..9] then 
        suff:=Concatenation("0",String(n));
    else
        suff:=String(n);
    fi;
    
    nameshort:=Concatenation("cc",suff);
    path:=PackageInfo("coco2p")[1].InstallationPath;
    name:=Concatenation(path,"cc/",nameshort,".g7.gz");
    lcode:=ReadG7File@(name);
    return Length(lcode);
end);

InstallGlobalFunction(SmallCoherentConfigurationsAvailable,
function(arg)
    
    if arg=[] then
        return smallCoherentConfigurationsAvailable@;
    fi;
    return arg[1] in smallCoherentConfigurationsAvailable@;
end);

    
InstallGlobalFunction(SmallCoherentConfiguration,
function(n,i)
    local  suff, nameshort, path, name, lcode, mat, cgr;
    
    if not SmallCoherentConfigurationsAvailable(n) then
        Info(InfoCOCO,1, Concatenation("SmallCoherentConfiguration: Only degrees ", 
                                       StringCocoList@(SmallCoherentConfigurationsAvailable())," are availably."));
        return fail;
    fi;
    if n in [0..9] then 
        suff:=Concatenation("0",String(n));
    else
        suff:=String(n);
    fi;
    
    nameshort:=Concatenation("cc",suff);
    path:=PackageInfo("coco2p")[1].InstallationPath;
    name:=Concatenation(path,"cc/",nameshort,".g7.gz");
    lcode:=ReadG7File@(name);
    if i > Length(lcode) then
        Info(InfoCOCO,1,Concatenation("SmallCoherentConfiguration: There are only ", String(Length(lcode))," association schemes of degree ", String(n),"."));
        return fail;
    fi;
    
    mat:=MatrixFromCode@(lcode[i]);
    cgr:=ColorGraphByMatrix(mat);
    SetIsWLStableColorGraph(cgr,true);
    SetName(cgr, Concatenation("CC(", String(n),",", String(i),")"));
    return cgr;
end);
    
# InstallGlobalFunction(AllCoherentConfigurations,
# function(n)
#     local   f,orders,  suff,  name, nameshort,res,tempvar,fnameshortreadonly;
    
#     orders:=[1..15];
    
#     if not n in orders then
#         Info(InfoCOCO,1, Concatenation("AllCoherentConfigurations: Only degrees ", StringCocoList@(orders)," are available.\n"));
#         return fail;
#     fi;
#     if n in [0..9] then 
#         suff:=Concatenation("0",String(n));
#     else
#         suff:=String(n);
#     fi;
    
#     nameshort:=Concatenation("cc",suff);
#     name:=Concatenation(nameshort,"@COCO2P");
    
    
#     if not IsBoundGlobal("cclist@COCO2P") then
#         f := SingleHTTPRequest( "my.svgalib.org", 80, "GET", "/math-data/ccs1_15n", rec( ), false, false );
#         if f.statuscode = 404  then
#             UnbindGlobal("cclist@COCO2P");
#             ErrorNoReturn( "File not found -- Check URL" );
#         elif f.statuscode >= 400  then
#             UnbindGlobal("cclist@COCO2P");
#             ErrorNoReturn( "HTTP error code ", f.statuscode );
#         fi;
#         f:=f.body;
#         f:=Concatenation("cclist@COCO2P:=",f,";");
#         Read( InputTextString( f ) );
#         MakeReadOnlyGlobal("cclist@COCO2P");
#     fi;
#     res:= List(ValueGlobal("cclist@COCO2P")[n], ColorGraphByMatrix);
#     Perform(res, function(x) SetIsWLStableColorGraph(x,true); end);
#     Perform([1..Length(res)], function(i) SetName(res[i], Concatenation("CC(", String(n),",", String(i),")")); end);
#     return res;
    
# end);
