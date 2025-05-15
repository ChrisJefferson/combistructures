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
gap> n := 4;;
gap> C := Combinatorial;;
gap> i1 := List([1..n], x -> C.Atom(x));;
gap> i2 := List([n+1..2*n], x -> C.Atom(x));;
gap> v := List([2*n+1..3*n], x -> C.Atom(x));;
gap> mat := [[1,2,3,4],[1,4,3,2], [1,2,4,3], [4,2,1,3]];;
gap> m := [];;
gap> for i in [1..4] do
>      l := List([1..4], j -> v[mat[i,j]]);
>      Add(m, C.Matrix(l, i2));
>    od;;
gap> fullm := C.Matrix(m, i1);;
gap> StabilizerOfFundamentalStructure(fullm, [1..3*n]);
