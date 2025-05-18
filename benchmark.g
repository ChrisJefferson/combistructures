Read("map.g");
Read("standard_mat.g");


count := 1;

for n in [20,40,80,160] do
    mat := List([1..n], x -> [1..n]);
    mapmat := makeMatExample(n, mat);
    parts := [[1..n], [n+1..2*n], [2*n+1..3*n]];
    omega := [1..3*n];

    total := 0;
    bliss := 0;

    for j in [1..count] do
        GASMAN("collect");
        x1 := NanosecondsSinceEpoch();
        grp := makeStandardMatrix(n, mat);
        x2 := NanosecondsSinceEpoch();
        total := total + (x2 - x1);
        bliss := bliss + _last_BlissAutomorphismGroup_time;
    od;

    total := total - bliss;
    Print(Int(total/1000/1000/count), "&",Int(bliss/1000/1000/count), " & ");

    for AtomOpt in [false, true] do
        #for TupleOpt in [false, true] do
            total := 0;
            bliss := 0;
            for j in [1..count] do
                DO_ATOM_OPT := AtomOpt;
                #DO_TUPLE_OPT := TupleOpt;
                GASMAN("collect");
                x1 := NanosecondsSinceEpoch();
                grp := StabilizerOfFundamentalStructure(mapmat, omega, parts);
                x2 := NanosecondsSinceEpoch();
                total := total + (x2-x1);
                bliss := bliss + _last_BlissAutomorphismGroup_time;
            od;
            total := total - bliss;
            Print(Int(total/1000/1000/count), "&",Int(bliss/1000/1000/count), " & ");
        #od;
    od;
    Print("\n");
od;



for n in [20,40,80,160] do
    mat := List([1..n], x -> [1..n]);
    mapmat := makeMatExample(n, mat);
    parts := [[1..n], [n+1..2*n], [2*n+1..3*n]];
    omega := [1..3*n];

    Print(3*n+n*n, "&", 3*n*n, " & ");

    for AtomOpt in [false, true] do
        #for TupleOpt in [false, true] do
            DO_ATOM_OPT := AtomOpt;
            #DO_TUPLE_OPT := TupleOpt;
            graph := _convertToDigraph(mapmat, omega, parts);
            Print(DigraphNrVertices(graph.graph), "&",DigraphNrEdges(graph.graph), " & ");
    #od;
    od;
    Print("\n");
od;
