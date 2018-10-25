# hashtables by  Gene Cooperman, Scott Murray, and  Alexander Hulpke
# canibalized from GAP 4.4   
# Original copyright statement follows:
#Y  Copyright (C)  1999,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1999 School Math and Comp. Sci., University of St.  Andrews, Scotland
#Y  Copyright (C) 2002 The GAP Group


BindGlobal("HASH_RANGE@",[0..10000]);
LastHashIndex@:=-1;

InstallGlobalFunction( HashTableSize@,
        hash -> hash.NumberKeys );

InstallGlobalFunction( GetHashEntryAtLastIndex@, function( hash )
    if IsBound( hash.ValueArray[ LastHashIndex@ ] ) then
        return( hash.ValueArray[ LastHashIndex@ ] );
    else 
        return fail;
    fi;
end );

InstallGlobalFunction( HashFunct@,
    function( key, i, size )
        # return ( (1+key) + i*(1+2*(key mod size/2)) ) mod size;
        return 1 + ( key + i * (1 + (key mod 2) + (key mod size)) ) mod size;   
    end );
    
    
InstallGlobalFunction( GetHashEntryIndex@, function( hash, key )
    local intkey, i, index;
    
    intkey := hash.intKeyFun(key);
    for i in HASH_RANGE@ do
        index := HashFunct@( intkey, i, hash.LengthArray );
        if hash.KeyArray[index] = fail or hash.KeyArray[index] = key then 
            LastHashIndex@ := index;
            return index;
        fi;
    od;
    Error("hash table in infinite loop");
end );

    
InstallGlobalFunction( SparseHashTable@, function(keyfun)
    local Rec,T;
    
    return rec( KeyArray := ListWithIdenticalEntries( DefaultHashLength, fail ), 
                   ValueArray := [], LengthArray := DefaultHashLength, NumberKeys := 0,
                   intKeyFun := keyfun );
end );


InstallGlobalFunction( DoubleHashArraySize@, function( hash )
    local oldKeyArray, oldValueArray, i;

    oldKeyArray := hash.KeyArray;
    oldValueArray := hash.ValueArray;
    hash.LengthArray := hash.LengthArray * 2;
    hash.LengthArrayHalf := Int(hash.LengthArray / 2);
    hash.KeyArray := ListWithIdenticalEntries( hash.LengthArray, fail );
    hash.ValueArray := [];
    hash.NumberKeys := 0;
    for i in [1..Length(oldKeyArray)] do
        if oldKeyArray[i] <> fail then
            AddHashEntry@( hash, oldKeyArray[i], oldValueArray[i] );
        fi;
    od;
end );

InstallGlobalFunction( AddHashEntry@,
    function( hash, key, value )
        local index;
        index := GetHashEntryIndex@( hash, key );
        if hash.KeyArray[ index ] = fail then
            hash.KeyArray[ index ] := key;
            hash.ValueArray[ index ] := value;
            hash.NumberKeys := hash.NumberKeys + 1;
            if 2 * hash.NumberKeys > Length( hash.KeyArray ) then
                DoubleHashArraySize@( hash );
            fi;

            return value;
        else 
            return fail;
        fi;
    end );
    
InstallGlobalFunction( GetHashEntry@, function( hash, key )
    local index, keyArray, valueArray;
    
    index := GetHashEntryIndex@( hash, key );
    if hash.KeyArray[index] = fail then
        return fail;
    fi;
    return hash.ValueArray[ index ]; 
end );
