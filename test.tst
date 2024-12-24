gap> Read("map.g");
gap> checkStabilizer := function(fs, omega, g)
> local gfs;
> gfs := StabilizerOfFundamentalStructure(fs, omega);
> if g <> gfs then
>  Print(fs, omega, g, gfs);
>  return false;
> fi;
> return true;
> end;;
gap> a2 := Combinatorial.Atom(2);;
gap> a4 := Combinatorial.Atom(4);;
gap> a2 = a4;
false
gap> a2 = OnFundamental(a4,(2,4));
true
gap> checkStabilizer(a2, [1..5], SymmetricGroup([1,3,4,5]));
true
gap> checkStabilizer(a4, [1..5], SymmetricGroup([1,2,3,5]));
true
gap> s1 := Combinatorial.Set([a2,a4]);;
gap> checkStabilizer(s1, [1..5], Group((1,3),(1,3,5),(2,4)));
true
gap> a3 := Combinatorial.Atom(3);;
gap> s2 := Combinatorial.Set([a3,a4]);;
gap> s1=s2;
false
gap> s1=OnFundamental(s2,(2,3));
true
gap> ss := Combinatorial.Set([s1,s2]);;
gap> checkStabilizer(ss, [1..5], Group((1,5),(2,3)));
true
gap> p1 := CanonicalPermOfFundamentalStructure(s1, [1..5]);;
gap> p2 := CanonicalPermOfFundamentalStructure(s2, [1..5]);;
gap> OnFundamental(s1, p1) = OnFundamental(s2, p2);
true
gap> g := Group((1,2,3,4,5));;
gap> p1 := CanonicalPermOfFundamentalStructureWithGroup(s1, [1..5], g);;
gap> p2 := CanonicalPermOfFundamentalStructureWithGroup(s2, [1..5], g);;
gap> OnFundamental(s1, p1) = OnFundamental(s2, p2);
false
gap> g := Group((2,3,4));;
gap> p1 := CanonicalPermOfFundamentalStructureWithGroup(s1, [1..5], g);;
gap> p2 := CanonicalPermOfFundamentalStructureWithGroup(s2, [1..5], g);;
gap> OnFundamental(s1, p1) = OnFundamental(s2, p2);
true
