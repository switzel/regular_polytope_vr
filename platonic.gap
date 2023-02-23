###############################################################################
### Code related to the article                                             ###
###                                                                         ###
### Vietoris-Rips complexes of platonic solids                              ###
### by Nada Saleh, Thomas Tits Mite, Stefan Witzel                          ###
###                                                                         ###
### Copyright by the authors.                                               ###
###############################################################################

LoadPackage("grape");
LoadPackage("Digraph");

A := [
    [20,1],[20,10],[20,19],
    [1,2],[1,8],
    [2,3],[2,6],
    [3,4],[3,19],
    [4,5],[4,17],
    [5,6],[5,15],
    [6,7],
    [7,8],[7,14],
    [8,9],
    [9,10],[9,13],
    [10,11],
    [11,12],[11,18],
    [12,13],[12,16],
    [13,14],
    [14,15],
    [15,16],
    [16,17],
    [17,18],
    [18,19]
];

RelDode := function(i,j)
    return [i,j] in A or [j,i] in A;
end;

dode := Graph(Group(()), [1..20], OnPoints, RelDode, true);

d := function(i,j)
    return Distance(dode, i, j);
end;

RelGamma := function(i,j)
    return d(i,j) in [1,2,3];
end;

gamma := Graph(Group(()), [1..20], OnPoints, RelGamma, true);

Distances := function(vertices)
    local pairs, shape;
    pairs := Combinations(vertices, 2);
    shape := List(pairs, x-> d(x[1], x[2]));
    Sort(shape);
    return shape;
end;

IsLarge := function(vertices)
    return (not Distances(vertices) = [3,3,3,3,3,3]) and (Length(vertices) > 0) and (3 in Distances(vertices));
end;

Shape := function(vertices)
    local n, p, pairs, shape;
    n := Length(vertices);
    pairs := Combinations([1..n], 2);
    shape := NullMat(n,n);
    for p in pairs do
        shape[p[1]][p[2]] := d(vertices[p[1]],vertices[p[2]]);
        shape[p[2]][p[1]] := d(vertices[p[1]],vertices[p[2]]);
    od;
    return shape;
 end;

Aut:=AutomorphismGroup(gamma);

Rot:=Group([ (1,12,3,9,17)(2,13,4,8,16)(5,7,15,6,14)(10,18,20,11,19),
  (1,10,12,15,6)(2,20,11,16,5)(3,19,18,17,4)(7,8,9,13,14) ]);

complex := List([1..7],x -> Filtered(CompleteSubgraphs(gamma,x), IsLarge));
matching := List([1..7],x -> []);
IsMatched := function(vertices)
    local n;
    n := Length(vertices);
    return vertices in List(matching[n],x -> x[1]) or vertices in List(matching[n-1],x -> x[2]);
end;

critical := List([1..7], k -> Filtered(complex[k], x -> not IsMatched(x)));

Match := function(upper, lower)
    local n;
    Assert(0,Length(upper) - Length(lower) = 1);
    n := Length(lower);
    Assert(0,not IsMatched(lower)); #, Concatenation("Simplex already matched ",String(lower),"\n"));
    Assert(0,not IsMatched(upper)); #, Concatenation("Simplex already matched ", String(upper),"\n"));
    Append(matching[n],[[lower,upper]]);
end;

MatchOrbit := function(upper, lower, group, stab_lower)
    local g, stab;
    if stab_lower then
        stab := Stabilizer(group, lower, OnSets);
    else
        stab := Stabilizer(group, upper, OnSets);
    fi;
    for g in RightTransversal(group, stab) do
        Match(OnSets(upper,g),OnSets(lower,g));
    od;
end;

DirectedEdge := function(a,b)
    local m,n;
    m := Length(a);
    n := Length(b);
    if AbsoluteValue(m-n) <> 1 then
        return false;
    fi;
    if m - n = 1 then
        return IsSubset(a,b) and not [b,a] in matching[n];
    fi;
    if n - m = 1 then
        return [a,b] in matching[m];
    fi;
    Assert(0,false);
end;


critical := List([1..7], k -> Filtered(complex[k], x -> not IsMatched(x)));
dhasse := Digraph(Rot,Concatenation(complex),OnSets,DirectedEdge);
UpdateCritical := function()
    critical := List([1..7], k -> Filtered(complex[k], x -> not IsMatched(x)));
    # The number of edges is less than
    # Sum(List([3..7],x -> Length(complex[x])*x));
    # because not every facet of a simplex in complex is in complex.
    dhasse := Digraph(Rot,Concatenation(complex),OnSets,DirectedEdge);
end;

AssessMatching := function()
    Print("Matching is complete: ",Length(Concatenation(critical)) = 0,"\n");
    Print("Matching is acyclic: ",IsAcyclicDigraph(dhasse),"\n");
end;

CriticalCofacets := function(simplex)
    local n;
    n := Length(simplex);
    return Filtered(critical[n+1],x -> IsSubset(x,simplex));
end;

CriticalCofacetsOfTransversal := function(n,group)
    return List(Orbits(group,critical[n],OnSets), o -> [o[1],CriticalCofacets(o[1])]);
end;

Main := function(k,g)
    local simplices, orbits, orbit, simplex;
    simplices := Filtered(complex[k],x -> not IsMatched(x));
    Print("There are ", Size(simplices), " ", k-1, "-Simplices. \n");
    orbits := Orbits(g, simplices, OnSets);
    Print("There are ", Size(orbits), " orbits of ", k-1, "-Simplices \n");
    for orbit in orbits do
        simplex := orbit[1];
        Print("Representative: ", simplex, " Shape: ", Distances(simplex), " Stabilizer: ", StructureDescription(Stabilizer(g, simplex, OnSets)), "\n");
    od;
end;

# "Imposed" by C3 symmetry
MatchOrbit([5,7,8,12,13,14,15],[5,7,8,12,13,15],Aut,false);
MatchOrbit([5,8,12,14],[5,8,12],Aut,false);

# Symmetry preserving
MatchOrbit([5,12,13,14,15,16],[5,12,13,14,16],Aut,false);
MatchOrbit([5,12,13,15],[5,12,13],Aut,false);

# Symmetry breaking and reappearing
MatchOrbit([5,7,12,13,14,15,16],[5,7,12,13,15,16],Rot,false);
MatchOrbit([5,7,12,13,14,16],[5,7,12,13,16],Rot,false);

MatchOrbit([5,7,13,14,15,16],[5,7,13,14,16],Aut,false);
MatchOrbit([5,7,13,15,16],[5,7,13,16],Aut,true);

MatchOrbit([5,13,14,15],[5,13,15],Rot,false);
MatchOrbit([5,12,15,16],[5,12,15],Rot,false);
MatchOrbit([5,13,14],[5,13],Rot,true);
MatchOrbit([5,12,16],[5,12],Rot,true);

MatchOrbit([5,7,12,14,15],[5,7,12,14],Rot,false);
MatchOrbit([5,7,12,15],[5,7,12],Rot,false);

# Asymmetric
MatchOrbit([5,12,14,15],[5,12,14],Aut,false);

MatchOrbit([5,8,12,14,15],[5,8,12,15],Aut,false);

MatchOrbit([5,7,12,14,15,16],[5,7,12,15,16],Aut,false);

MatchOrbit([5,7,8,12,14,15],[5,7,8,12,15],Aut,false);

MatchOrbit([5,7,12,13,15],[5,7,12,13],Aut,false);
MatchOrbit([5,12,13,15,16],[5,12,13,16],Aut,false);
MatchOrbit([5,12,14,15,16],[5,12,14,16],Aut,false);

UpdateCritical();
AssessMatching();
