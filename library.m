// DiscriminantGroup
// Input: A matrix with integer coefficients
// Output: Its discriminant group and the quadratic form in Q/2Z

// DiscriminantGroup
// Input: an integer matrix M
// Output:
//   1. the invariant factors of the discriminant group
//   2. the quadratic form matrix in Q/2Z
//   3. the generators of the discriminant group as columns in L^vee

function DiscriminantGroup(M)
    S, A, B := SmithForm(M);

    inds := [ i : i in [1..NumberOfColumns(S)] | S[i,i] notin {0,1} ];
    invs := [ S[i,i] : i in inds ];

    if #inds eq 0 then
        return [], ZeroMatrix(Rationals(),0,0), ZeroMatrix(Rationals(), NumberOfRows(M), 0);
    end if;

    gens := Matrix(Rationals(), ColumnSubmatrix(B, inds));
    for k in [1..#inds] do
        MultiplyColumn(~gens, 1/invs[k], k);
    end for;

    Q := Transpose(gens) * Matrix(Rationals(), M) * gens;

    for i, j in [1..NumberOfRows(Q)] do
        if i ne j then
            Q[i,j] := Q[i,j] - Floor(Q[i,j]);
        else
            Q[i,j] := Q[i,j] - Floor(Q[i,j]) + (Floor(Q[i,j]) mod 2);
        end if;
    end for;

    return invs, Q, gens;
end function;

// MatrixMod2
// Input: A matrix with rational coefficients
// Output: The matrix with its entries reduced modulo 2

MatrixMod2 := function(Q);
    for i, j in [1..Nrows(Q)] do
        if i ne j then 
            Q[i, j] := Q[i, j] - Floor(Q[i, j]);
        else 
            Q[i, j] := Q[i, j] - 2 * Floor(Q[i, j] / 2);
        end if;
    end for;
    return Q;
end function;

// IsotropicElements
// Input: A matrix with integer coefficients
// Output: The null elements of its discriminant group

IsotropicElements := function(M);
    // Compute the discriminant group and quadratic form
    v, U := DiscriminantGroup(M);
    Q := Rationals();
    // Define an abelian group with orders from the discriminant group
    A := AbelianGroup(v);
    // Return elements that are isotropic with respect to the quadratic form
    return [Eltseq(a) : a in A | 
            MatrixMod2(Matrix(Q, 1, #v, Eltseq(a)) * U * Matrix(Q, #v, 1, Eltseq(a)))[1, 1] eq 0];
end function;

// CompareDiscriminants
// Input: Two matrices M and Q with integer coefficients
// Output: True if the discriminant group and quadratic form of M and Q are equivalent, false otherwise

CompareDiscriminants := function(M, Q)
    // Compute the discriminant group and quadratic form for M
    v, U := DiscriminantGroup(M);
    // Compute the discriminant group and quadratic form for Q
    w, D := DiscriminantGroup(Q);

    // If the discriminant groups have different orders, return false
    if v ne w then 
        return false;
    end if;

    // Create an abelian group from the discriminant group
    A := AbelianGroup(v);
    // Compute the automorphism group of A
    Aut := AutomorphismGroup(A);
    // Obtain the permutation representation of the automorphism group
    f, G := PermutationRepresentation(Aut);
    h := Inverse(f); // Inverse map for automorphisms

    // Compute the matrices representing automorphisms
    ll := [Matrix(Rationals(), [Eltseq((h(g))(A.i)) : i in [1..Ngens(A)]]) : g in G];
    // Apply each automorphism to the quadratic form and reduce modulo 2
    dd := [MatrixMod2(a * U * Transpose(a)) : a in ll];

    // Check if the quadratic form of Q is equivalent to any transformed form of M
    return D in dd;
end function;
