Read("map.g");
Read("standard_mat.g");


count := 10;

for n in [20,40,60,80] do
    mat := List([1..n], x -> [1..n]);
    mapmat := makeMatExample(n, mat);
    parts := [[1..n], [n+1..2*n], [2*n+1..3*n]];
    omega := [1..3*n];

    for j in [1..count] do
        total := 0;
        x1 := NanosecondsSinceEpoch();
        grp := makeStandardMatrix(n, mat);
        x2 := NanosecondsSinceEpoch();
        total := x2 - x1;
    od;
    Print(Int(total/1000/count), "\t&");

    for AtomOpt in [false, true] do
        for TupleOpt in [false, true] do
            for j in [1..count] do
                DO_ATOM_OPT := AtomOpt;
                DO_TUPLE_OPT := TupleOpt;
                x1 := NanosecondsSinceEpoch();
                grp := StabilizerOfFundamentalStructure(mapmat, omega, parts);
                x2 := NanosecondsSinceEpoch();
                total := x2-x1;
            od;
            Print(Int(total/1000/count), "\t&");
        od;
    od;
    Print("\n");
od;



for n in [20,40,60,80] do
    mat := List([1..n], x -> [1..n]);
    mapmat := makeMatExample(n, mat);
    parts := [[1..n], [n+1..2*n], [2*n+1..3*n]];
    omega := [1..3*n];

    Print(3*n+n*n, "&", 3*n*n, " & ");

    for AtomOpt in [false, true] do
        for TupleOpt in [false, true] do
            DO_ATOM_OPT := AtomOpt;
            DO_TUPLE_OPT := TupleOpt;
            graph := _convertToDigraph(mapmat, omega, parts);
            Print(DigraphNrVertices(graph.graph), "&",DigraphNrEdges(graph.graph), " & ");
    od;
    od;
    Print("\n");
od;
