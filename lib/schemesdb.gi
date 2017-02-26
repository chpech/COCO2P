InstallGlobalFunction(AllAssociationSchemes,
function(n)
    local   orders,  suff,  name, nameshort,res,tempvar,fnameshortreadonly;
    
    orders:=Difference([1..40],[1,2,3,4,31,35,36,37,39,40]);
    
    if not n in orders then
        Error("Only degrees ", orders," are availably.");
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
