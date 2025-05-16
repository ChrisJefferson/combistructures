LoadPackage("digraphs", false);

FixCanonicalLabelling := function(n, p, colours)
    local colmap, i, j, listperm, colnext, newperm, val, col;

    # Sort the members of each colour class.
    colours := List(colours, Set);

    colmap := ListWithIdenticalEntries(n, 0);

    for i in [1..Length(colours)] do
        for j in colours[i] do
            colmap[j] := i;
        od;
    od;

    listperm := ListPerm(p^-1, n);
    
    colnext := ListWithIdenticalEntries(Length(colours), 1);
    
    newperm := ListWithIdenticalEntries(n, 0);

    for i in [1..n] do
        val := listperm[i];
        # Get the colour of the ith vertex
        col := colmap[val];
        
        # That vertex goes to the next free space in it's colour class
        newperm[val] := colours[col][colnext[col]];
        colnext[col] := colnext[col] + 1;
    od;

    # Print(colnext, newperm);

    return PermList(newperm);
end;