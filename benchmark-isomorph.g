Read("map.g");
Read("standard_mat.g");
Read("isomorphDesign.g");


count := 10;
setmult := 20;


mkGrp := function(n)
    local g, gens;
    g := DirectProduct(SymmetricGroup(n/2),SymmetricGroup(n/2));
    gens := GeneratorsOfGroup(g);
    gens := Concatenation(gens, [PermList(Concatenation([n/2+1..n],[1..n/2]))]);
    g := Group(gens);
    Size(g);
    return g;
end;

for conf in [ 
     [{n}->false, false], [{n} -> [[1..n/2],[n/2..n]], false]
    #,[{n}->false, true]
    ]
    do
mkIccFunc := conf[1];
useGrp := conf[2];

optGrp := false;

for n in [80,160,320,640] do
    m := randomMat(n, n*setmult);

    total := 0;
    bliss := 0;
    # optgrp := mkGrp(n);

    for j in [1..count] do
        GASMAN("collect");
        x1 := NanosecondsSinceEpoch();
        mat := makeStandardMatGraph(n,n*setmult, m, mkIccFunc(n));
        grp := _time_BlissAutomorphismGroup(mat.graph, mat.colours);
        x2 := NanosecondsSinceEpoch();
        total := total + (x2 - x1);
        bliss := bliss + _last_BlissAutomorphismGroup_time;
    od;

    total := total - bliss;
    Print(Int(total/1000/1000/count), "&",Int(bliss/1000/1000/count), " & ");

    for AtomOpt in [false, true] do
            total := 0;
            bliss := 0;
            for j in [1..count] do
                DO_ATOM_OPT := AtomOpt;
                GASMAN("collect");
                x1 := NanosecondsSinceEpoch();
                mat2 := makeCombinatorialMat(n,n*setmult, m, mkIccFunc(n));
                if useGrp then
                    grp := StabilizerOfFundamentalStructureWithGroup(mat2, [1..n], optgrp);
                else
                    grp := StabilizerOfFundamentalStructure(mat2, [1..n]);
                fi;
                x2 := NanosecondsSinceEpoch();
                total := total + (x2-x1);
                bliss := bliss + _last_BlissAutomorphismGroup_time;
            od;

            total := total - bliss;
            Print(Int(total/1000/1000/count), "&",Int(bliss/1000/1000/count), " & ");
    od;
    Print("\n");
od;


for n in [80,160,320,640] do
    m := randomMat(n, n*setmult);
    mat := makeStandardMatGraph(n,n*setmult, m, mkIccFunc(n));
    mat2 := makeCombinatorialMat(n,n*setmult, m, mkIccFunc(n));

    Print(DigraphNrVertices(mat.graph), "&", DigraphNrEdges(mat.graph), " & ");

    for AtomOpt in [false, true] do
            DO_ATOM_OPT := AtomOpt;
            graph := _convertToDigraph(mat2, [1..n], [[1..n]]);
            Print(DigraphNrVertices(graph.graph), "&", DigraphNrEdges(graph.graph), " & ");

    od;
    Print("\n");
od;

Print("\n\n\n");

od;