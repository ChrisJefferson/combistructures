LoadPackage("digraphs", false);
Read("map.g");

randomMat := function(n,m)
    return List([1..m], x -> List([1..n], y -> Random([0,1])));
end;

# icc is 'interchangable colours', it is a partition of n (or false)
makeStandardMatGraph := function(n,m,mat, icc)
    local edges, i, j, cols;
    # Set up vertices
    edges := List([1..n+m], x -> []);
    for i in [1..m] do
        for j in [1..n] do
            if mat[i,j] = 1 then
                Add(edges[i+n],j);
            fi;
        od;
    od;
    if IsList(icc) then
        cols := [[1..n],[n+1..n+m],[n+m+1..n+m+Length(icc)]];
        for i in [1..Length(icc)] do
            Add(edges, []);
            for j in icc[i] do
                Add(edges[n+m+i], j);
            od;
        od;
    else
        cols := [[1..n],[n+1..n+m]];
    fi;

    return rec(graph := Digraph(edges), colours := cols);
end;

makeCombinatorialMat := function(n,m,mat)
    local set, i, j, member;
    # Set up vertices
    set := [];
    for i in [1..m] do
        member := [];
        for j in [1..n] do
            if mat[i,j] = 1 then
                Add(member,j);
            fi;
        od;
        Add(set, Combinatorial.Set(member));
    od;
    return Combinatorial.Set(set);
end;
