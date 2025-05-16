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

for mkIccFunc in [{n} -> false, {n} -> [[1..n/2],[n/2..n]]] do

for n in [100,200,400,800] do
    m := randomMat(n, n*setmult);

    for j in [1..count] do
        total := 0;
        GASMAN("collect");
        x1 := NanosecondsSinceEpoch();
        mat := makeStandardMatGraph(n,n*setmult, m, mkIccFunc(n));
        grp := BlissAutomorphismGroup(mat.graph, mat.colours);
        x2 := NanosecondsSinceEpoch();
        total := x2 - x1;
    od;
    Print(Int(total/1000/count), "\t&");

    for AtomOpt in [false, true] do
        for TupleOpt in [false, true] do
            for j in [1..count] do
                DO_ATOM_OPT := AtomOpt;
                DO_TUPLE_OPT := TupleOpt;
                GASMAN("collect");
                x1 := NanosecondsSinceEpoch();
                mat2 := makeCombinatorialMat(n,n*setmult, m, mkIccFunc(n));
                grp := StabilizerOfFundamentalStructure(mat2, [1..n]);
                x2 := NanosecondsSinceEpoch();
                total := x2-x1;
            od;
            Print(Int(total/1000/count), "\t&");
        od;
    od;
    Print("\n");
od;


for n in [50,100,150,200] do
    m := randomMat(n, n*setmult);
    mat := makeStandardMatGraph(n,n*setmult, m, mkIccFunc(n));
    mat2 := makeCombinatorialMat(n,n*setmult, m, mkIccFunc(n));

    Print(DigraphNrVertices(mat.graph), "&", DigraphNrEdges(mat.graph), " & ");

    for AtomOpt in [false, true] do
        for TupleOpt in [false, true] do
            DO_ATOM_OPT := AtomOpt;
            DO_TUPLE_OPT := TupleOpt;
            graph := _convertToDigraph(mat2, [1..n], [[1..n]]);
            Print(DigraphNrVertices(graph.graph), "&", DigraphNrEdges(graph.graph), " & ");

        od;
    od;
    Print("\n");
od;

Print("\n\n\n");

od;