makeStandardMatrix := function(n, matrix)
    local i1, i2, val, mat, vert, i, j, cols, edges, group;

    i1 := 0;
    i2 := n;
    val := 2*n;
    mat := 3*n;

    vert := function(x,y)
        return mat + (x-1)*n + (y);
    end;

    edges := List([1..mat+n*n], x -> []);
    for i in [1..n] do
        for j in [1..n] do
            Add(edges[vert(i,j)], i1+i);
            Add(edges[vert(i,j)], i2+j);
            Add(edges[vert(i,j)], val + matrix[i][j]);
        od;
    od;

    d := Digraph(edges);

    cols := [[1..n],[n+1..2*n],[2*n+1..3*n],[3*n+1..3*n+n*n]];

    if false then
        group := VoleFind.Group(SymmetricGroup(3*n+n*n),
        [
            Constraint.Stabilize(d, OnDigraphs),
            Constraint.Stabilize(cols, OnTuplesSets)
        ]);
    else
        group := BlissAutomorphismGroup(d, cols);
    fi;

    group := Group(List(GeneratorsOfGroup(group), x -> RestrictedPerm(x, [1..3*n])));

    return group;
end;

n := 80;
mat := List([1..n], x -> [1..n]);

grp := makeStandardMatrix(n, mat);
