LoadPackage("datastructures", false);
LoadPackage("vole", false);

Fundamental := rec();

_CollectionTuple := function(l, type)
    return Fundamental.CollectionOfWithType(
        List(l, x -> Fundamental.TupleOfWithType(List(x, y -> Fundamental.AtomOf(y)))), type
    );
end;

Combinatorial := rec(
    Atom := function(a)
        return Fundamental.AtomOfWithType(a, "atom");
    end,

    Set := function(l)
        return Fundamental.CollectionOfWithType(l, "set");
    end,

    Multiset := function(l)
        return Fundamental.CollectionOfWithType(l, "multiset");
    end,

    Tuple := function(l)
        return Fundamental.TupleOfWithType(l, "tuple");
    end,

    Permutation := function(p)
        local moved;
        moved := List(MovedPoints(p), x -> [x,x^p]);
        return _CollectionTuple(moved, "permutation");
    end,

    Transformation := function(p)
        local moved;
        moved := List(MovedPoints(p), x -> [x,x^p]);
        return _CollectionTuple(moved, "transformation");
    end,

    PartialPermutation := function(p)
        local moved;
        moved := List(MovedPoints(p), x -> [x,x^p]);
        return _CollectionTuple(moved, "partialpermutation");
    end,


);

Fundamental := rec(

AtomType := 0,
CollectionType := 1,
TupleType := 2,

AtomVertex := 3,
OtherVertex := 3,

PAtom := "PAtom",

AtomOf := function(a)
    return rec(kind := Fundamental.AtomType, contents := a, type := "");
end,

AtomOfWithType := function(a, t)
    return rec(kind := Fundamental.AtomType, contents := a, type := t);
end,

CollectionOf := function(l)
    l := SortedList(l);
    return rec(kind := Fundamental.CollectionType, contents := l, type := "");
end,

CollectionOfWithType := function(l, t)
    l := SortedList(l);
    return rec(kind := Fundamental.CollectionType, contents := l, type := t);
end,

TupleOf := function(l)
    return rec(kind := Fundamental.TupleType, contents := l, type := "");
end,

TupleOfWithType := function(l, t)
    return rec(kind := Fundamental.TupleType, contents := l, type := t);
end
);


OnFundamental := function(f,p)
    local ret;
    ret := rec(kind := f.kind, type := f.type);
    if f.kind = Fundamental.AtomType then
        ret.contents := f.contents^p;
    elif f.kind = Fundamental.CollectionType then
        ret.contents := List(f.contents, x -> OnFundamental(x,p));
        Sort(ret.contents);
    elif f.kind = Fundamental.TupleType then
        ret.contents := List(f.contents, x -> OnFundamental(x,p));
    else
        Assert(0, "Invalid kind");
    fi;
    return ret;
end;

_newVertex := function(graph, colour, height)
    local vert;
    vert :=  rec(name := [Length(graph.vertices), Fundamental.OtherVertex], colour := colour, height := height, id := Length(graph.vertices)+1);
    Add(graph.vertices,vert);
    return vert;
end;

_idOfOmega := function(graph, o)
    local v;
    v := First(graph.vertices, x -> x.name = [o, Fundamental.AtomVertex]);
    if v = fail then
        Error(String(o) + " is not an element of Omega");
    fi;
    return v.id;
end;

_buildGraph := function(graph, o)
        local v, children,max, i, c;
        max := 1;
        if o.kind = Fundamental.AtomType then
            v := _newVertex(graph, "atom", 1);
            Add(graph.edges, [_idOfOmega(graph, o.contents), v.id]);
            return v;
        elif o.kind = Fundamental.CollectionType then
            children := List(o.contents, x -> _buildGraph(graph, x));
            for c in children do
                max := Maximum(c.height, max);
            od;

            v := _newVertex(graph, "collection",max);

            for c in children do
                Add(graph.edges, [v.id, c.id]);
                max := Maximum(c.height, max);
            od;

            return v;
        elif o.kind = Fundamental.TupleType then
            v := [];
            children := List(o.contents, x -> _buildGraph(graph, x));
            max := Maximum(Concatenation([0], List(children, x -> x.height)));
            for i in [1..Length(children)] do
                Add(v, _newVertex(graph, Concatenation("tuple", String(i)), max));
                Add(graph.edges, [v[i].id, children[i].id]);
                if i <> 1 then
                    Add(graph.edges, [v[i].id, v[i-1].id]);
                fi;
            od;
            return v[1];
        fi;

        Assert(0, "Invalid kind: ", o.kind);
end;

# The vertices in Omega are always put at the start
GraphOfFundamentalStructure := function(s, omega)
    local graph, i;


    graph := rec(vertices := [], edges := [], omega := Length(omega));

    Append(graph.vertices, List(omega, x -> rec(name := [x, Fundamental.AtomVertex], colour := Fundamental.PAtom, height := 1)));

    for i in [1..Length(graph.vertices)] do
        graph.vertices[i].id := i;
    od;

    _buildGraph(graph, s);

    return graph;
end;

_convertToDigraph := function(fs, omega)
    local g, e, c, edges, colourset, colourtupleset;
    g := GraphOfFundamentalStructure(fs, omega);
    edges := List(g.vertices, x -> []);
    for e in g.edges do
        Add(edges[e[1]], e[2]);
    od;

    colourset := Set(g.vertices, x -> x.colour);
    colourtupleset := List(colourset, x -> []);
    for c in g.vertices do
        Add(colourtupleset[Position(colourset, c.colour)], c.id);
    od;
    return rec(graph := Digraph(edges), colours := colourtupleset);
end;

StabilizerOfFundamentalStructure := function(fs, omega)
    local g, group;
    g := _convertToDigraph(fs, omega);
    group := VoleFind.Group(
        SymmetricGroup(DigraphVertices(g.graph)),
        [
        Constraint.Stabilize(g.graph, OnDigraphs),
        Constraint.Stabilize(g.colours, OnTuplesSets)
        ]
    );

    group := Group(List(GeneratorsOfGroup(group), x -> RestrictedPerm(x, [1..Length(omega)])));
    return group;
end;

StabilizerOfFundamentalStructureWithGroup := function(fs, omega, grp)
    local g, group, cangroup;
    g := _convertToDigraph(fs, omega);
    cangroup := Group(Concatenation(GeneratorsOfGroup(grp), GeneratorsOfGroup(SymmetricGroup([Length(omega)+1..DigraphNrVertices(g.graph)]))));
    group := VoleFind.Group(cangroup,
        [
        Constraint.Stabilize(g.graph, OnDigraphs),
        Constraint.Stabilize(g.colours, OnTuplesSets)
        ]
    );

    group := Group(List(GeneratorsOfGroup(group), x -> RestrictedPerm(x, [1..Length(omega)])));
    return group;
end;


CanonicalPermOfFundamentalStructureWithGroup := function(fs, omega, grp)
    local g, perm, cangroup;
    g := _convertToDigraph(fs, omega);
    cangroup := Group(Concatenation(GeneratorsOfGroup(grp), GeneratorsOfGroup(SymmetricGroup([Length(omega)+1..DigraphNrVertices(g.graph)]))));
    perm := VoleFind.CanonicalPerm(cangroup,
        [
        Constraint.Stabilize(g.graph, OnDigraphs),
        Constraint.Stabilize(g.colours, OnTuplesSets)
        ]
    );
    return RestrictedPerm(perm, [1..Length(omega)]);
end;

CanonicalPermOfFundamentalStructure := function(fs, omega)
    return CanonicalPermOfFundamentalStructureWithGroup(fs, omega, SymmetricGroup(omega));
end;
