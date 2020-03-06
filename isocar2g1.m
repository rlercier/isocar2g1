/***
 *  Fast Computation of Elliptic Curve Isogenies in Characteristic two
 *
 *  Distributed under the terms of the GNU Lesser General Public License (L-GPL)
 *                  http://www.gnu.org/licenses/
 *
 *  Copyright (C) 2020 X. Caruso, E. Eid & R. Lercier
 */


 /*
   The following is a self-contained magma script that implements
   the algorithms of the paper "Fast Computation of Elliptic Curve
   Isogenies in Characteristic two" by X. Caruso, E. Eid & R. Lercier.

   Usage: "magma isocar2g1.m"
          (tested on Magma V2.24-10)
*/


// Some defines
Iso_t := recformat<A, B, AB, a, b, ba, ainv, Qa, Ra, Ra3>;
forward DiffSolve, MySqrtInv, MyInv;


// Main function : We look for an isogeny from
//   y^2 = x^3 + x^2/4 + A
// to
//   y^2 = x^3 + x^2/4 + B
// A, B, and the isogeny differential c = AB, are defined over the 2-adics

// The result is an isogeny series, up to precision 2*ell+2

function IsoSolve(ell, _A, _B, _AB)

    /* Precomputations... */
    CK := Parent(_A);
    PDef := DefiningPolynomial(CK);
    p := Prime(CK); M := Precision(_A);
    K := pAdicQuotientRing(p, M); if PDef ne Parent(PDef).1-1 then
	K<u> := UnramifiedExtension(K, DefiningPolynomial(CK));
    end if;

    x := PolynomialRing(K).1;
    L := LaurentSeriesRing(K : Precision := 2*ell+3); t := L.1;

    A  := K!ChangeUniverse(Eltseq(_A), Integers());
    B  := K!ChangeUniverse(Eltseq(_B), Integers());
    AB := K!ChangeUniverse(Eltseq(_AB), Integers());

    /* a and b */
    a := HenselLift(4*A*x^3 + x + 4, K!4);
    b := HenselLift(4*B*x^3 + x + 4, K!4);

    ba := b div a;
    ainv := (a div 4)^-1;

    /* 1 / u(t) */
    N := 2*ell + 1; M :=Ceiling((N)/2);

    Cste := A div (4*A*a^2+1);
    r0 := (Sqrt(1 + 4*A*a^2))^-1;
    r1 := - 2*a*r0 * Cste;
    r2 := - ( 2*r0 + 3*a*r1 ) * Cste;

    Ra, _ :=
	MySqrtInv(4*A*t^2+4*A*a*t+4*A*a^2+1, N-M : PRC0 := [* 2, [* r0 + r1*t + r2*t^2 *] *] );

    /* u(t) */
    Qa := (4*A*t^2+4*A*a*t+4*A*a^2+1) * Ra;

    /* u(t)^3 */
    Ra3 := (Ra^2) * Ra;

    /* Isogeny solver */
    Prc := rec<Iso_t | A := A, B := B, AB := AB, a := a, b:=b, ba:= ba, ainv := ainv, Qa := Qa, Ra := Ra, Ra3 := Ra3>;

    T0 := DiffSolve(N, Prc);

    return  t* ( Prc`ba + (t-Prc`a)*T0 );

end function;

function DiffSolve(N, Prc);

    L := Parent(Prc`Qa); t := L.1; K := Parent(Prc`a); PR := PolynomialRing(K);
    x := PolynomialRing(Parent(Prc`AB)).1;

    /*
     * Initialisation
     ****************/
    if N eq 0 then

	t1 := (Prc`ba - Prc`AB) div Prc`a;
	if Valuation(t1) lt 0 then return 0*t, K!0, [], []; end if;
        return
            t1+ O(t^( N+1)),
            [* 0, [**] *] ;
    end if;


    /*
     * Recursive call
     ****************/
    M :=Floor(N/2);

    T0_tilde, PRC0 := DiffSolve(M, Prc);
    if T0_tilde eq 0 then return T0_tilde, [], []; end if;
    ChangePrecision(~T0_tilde, N+1);

    /*
     * From M+1 to N
     ***************/

    /* z */
    T00:= Prc`ba + (t-Prc`a)*T0_tilde;
    T0:= t*T00;

    /* T2 := T'^2 */
    Tp := Derivative(T0);
    Tp2 := Tp^2;

    // The RHS, s, of the equadiff
    G  := (4*Prc`A*t^2+4*Prc`A*Prc`a*t+4*Prc`A*Prc`a^2+1) * Tp2;
    G  := L![ Coefficient(G,i+M) : i in [0..(N-M)] ] + O(t^(N-M+1));

    VatT0 := 4*Prc`b*T0;
    T2 := T0^2; VatT0 +:= 4*T2;
    VatT0 *:= Prc`B;
    VatT0 +:= 1+ 4*Prc`B*Prc`b^2;
    VatT0 *:= Prc`ba + t*T0_tilde;
    VatT0 *:= T00;
    VatT0  := L![ Coefficient(VatT0,i+M) : i in [0..(N-M)] ] + O(t^(N-M+1));
    G -:=  Prc`AB * VatT0;

    // 1/T'^2
    T2i, PRC := MyInv(Tp2, N-M : PRC0 := PRC0);

    // f
    F := G*Prc`Ra3;
    F *:= T2i;

    // The solution Y (LinDiffSolve algorithm)
    yi := [K!0 : i in [0..N-M]];
    for i := 1 to N-M do
	yi[1+i] := ((Coefficient(F, i) + K!(2*(M+i)) * yi[1+i-1])) div (8*(M+i)+4);
	yi[1+i] *:= Prc`ainv;
    end for;
    YT := L!yi + O(t^(N-M+1));

    // And then, the result q
    dT := YT * Tp; dT *:= Prc`Qa; dT *:= t^M;
    T1 := ChangePrecision(T0_tilde +  dT, N+1);

    return T1, PRC;

end function;

// 1 / sqrt(A) computed with a Newton iteration
// --------------------------------------------
function MySqrtInv(A, N : PRC0 := [* 2, [**] *] )

    L := Parent(A); t := L.1;
    K := BaseRing(L); PR := PolynomialRing(K);

    // Initial condition
    N0 := PRC0[1];
    if N le N0 then return PRC0[2, 1]; end if;

    // Let us recurse
    M := Max(N0, (N+2) div 2);
    R := MySqrtInv(A, M : PRC0 := PRC0);
    _A := ChangePrecision(A, N+1); _R := ChangePrecision(R, N+1);

    // Newton iteration

    /* R^2 */
    H := -_R^2;

    /* 3-A*R^2 */
    H *:= _A; H +:= 3;

    /* (3-A*R^2)/2 */
    Cof, v := Coefficients(H);
    H := L!Coefficients((PR!Cof) div 2); if v ne 0 then H *:= t^v; end if; ChangePrecision(~H, N+1);

    /* R*(3-A*R^2)/2 */
    H *:= _R;

    return H;

end function;


// 1 / A computed with a Newton iteration
// --------------------------------------
function MyInv(A, N : PRC0 := [* 0, [**] *])

    L := Parent(A); t := L.1;

    if N lt PRC0[1] or N eq 0 then
	if #(PRC0[2]) eq 0 then
	    H := Coefficient(A, 0)^(-1) + O(t);
	    return H, [* 0, [* H *] *];
	end if;
	return PRC0[2, 1], PRC0;
    end if;

    // Let us recurse
    B, _ := MyInv(A, N div 2 : PRC0 := PRC0);
    ChangePrecision(~B, N+1);

    H  := 2 - B * ChangePrecision(A, N+1);
    H *:= B;

    return H, [* N, [* H *] *];

end function;


// Half GCD (from Thome's PHD)
// ---------------------------
function PartialGCD(U, V, z, s)

    Px := Parent(U); X := Px.1; n := Degree(U);

    if s gt Degree(V) then
	return IdentityMatrix(Px, 2);
    end if;

    if s eq Degree(V) then
	return Matrix(2,2,[Px | 0, 1, 1, - (U div V) ]);
    end if;

    m := s - (n - z);
    pi_left := $$(U div X^m, V div X^m, z-m, Ceiling((z+s)/2)-m);

    next := Vector([U, V])*pi_left;
    nU := next[1]; nV := next[2];

    m := 2*s - Degree(nU);
    pi_right := $$(nU div X^m, nV div X^m, Ceiling((z+s)/2)-m,s-m);

    return pi_left * pi_right;

end function;


// Find A and B s.t. T = A / B
// ---------------------------
function FastBerlekampMassey(ell, T)

    L := Parent(T); t := L.1;
    K := CoefficientRing(L); PR := PolynomialRing(K); x := PR.1;

    U := x^(2*ell);

    C, v := Coefficients(T);
    V := (x^v * Parent(x)!C) mod U;

    // PartialGCD
    PI := PartialGCD(U, V, (2*ell), (2*ell +1) div 2);

    /* A & B */
    A := V*PI[2, 2] mod x^(2*ell);
    B := PI[2, 2];

    return A, B;

end function;

// Get the Elkies polynomial from the isogeny series
// -------------------------------------------------
function PadicToF2Iso(ell, T)

    L := Parent(T); K := BaseRing(L);

    FF, redmap := ResidueClassField(K);
    Px := PolynomialRing(FF); x := Px.1;

    Lp := ChangeRing(L, FF);

    /* Fast Berlekamp Massey */
    Num, _ := FastBerlekampMassey(ell+1, Lp!T);

    /* Square root */
    isq, sqrt := IsSquare(Num div x);

    return  (isq select Reverse(sqrt) else Px!0);

end function;

// Application to the multiplication by ell
// ----------------------------------------

/* GF(p^n) : n can be changed to some other degree */
p := 2; n := 1;

/* The starting elliptic curve */
BK := pAdicField(p, 32); K := BK;
K := BK; if n ne 1 then
    K<u> := UnramifiedExtension(BK, n);
end if;
_<x> := PolynomialRing(K);

FF, redmap := ResidueClassField(RingOfIntegers(K));
_<v> := FF;
_<z> := PolynomialRing(FF);

repeat
    a := Random(FF);
until IsEllipticCurve([1,0,0,0,a]);
E := EllipticCurve([1,0,0,0,a]);

eKa := EllipticCurve( [ K!Eltseq(x) : x in Eltseq(E)]);
EKa, _ := WeierstrassModel(eKa);
_, _, _, a4, a6 := Explode(Eltseq(EKa));

Aa := Sqrt(-1/27*a4); Ba := Sqrt(Aa^3);
_A := 1/46656*(a6/Aa^3)-1/864;

/* Let's go ! */
el := 11; Timings := [];
repeat

    DPE := 1;
    el  := NextPrime(el); ell := el^2;
    M := Floor(Log(2, ell)) + 6 /* 1 */;

    "---";
    "- el =", el, ", ell =", ell, ", M = ", M;
    "-------------------";

    EKb := EllipticCurve([0, 0, 0, ell^2*a4, ell^3*a6]);
    _, _, _, b4, b6 := Explode(Eltseq(EKb));

    "\n2-adic Isogeny from\n", EKa, "to\n", EKb;

    _, Ab := IsSquare(-1/27*b4);
    _, Bb := IsSquare(Ab^3);
    _B :=  1/46656*(b6/Ab^3)-1/864;

    _AB := Sqrt(b4/a4);

    // Solve the differential equation over the padics
    ChangePrecision(~_A,  M);
    ChangePrecision(~_B,  M);
    ChangePrecision(~_AB, M);

    Tm0 := Cputime();
    T := IsoSolve(ell, _A, _B, _AB); "";
    Tm0 := Cputime(Tm0);
    printf "Diff. equ. solved in %.2o s\n", Tm0;

    if T eq 0 then "Argh, T = 0 !"; break;  end if;

    // The GF(2^n) solution
    Tm1 := Cputime();
    elkiespol := PadicToF2Iso(ell, T);
    Tm1 := Cputime(Tm1);
    printf "Reconstruction done in %.2o s\n", Tm1;

    if Degree(elkiespol) ne ((ell -1) div 2) then
        if T eq 0 then "Argh, Degree(psi) != (ell-1)/2 !"; break;  end if;
    end if;

    // Let us check it
    Embed(FF, CoefficientRing(elkiespol));
    Tm2 := Cputime();
    DPE := DivisionPolynomial(E, el, elkiespol);
    Tm2 := Cputime(Tm2);
    printf "Check done in %.2o s\n\n", Tm2;

    "Elkies polynomial check:", DPE eq 0; "";

    // Timing output
    if DPE eq 0 then

        Append(~Timings, [* ell, Tm0, Tm1, Tm2 *]);
        Fields := [
            "ell", "DiffEq", "Recons", "Check"
            ];

        "Timings :\n";
        printf " ";
        for f in Fields do printf "| %o\t\t", f; end for;
        printf "\n";

        for L in Timings do
            printf " %o\t\t", L[1];
            for l in L[2..#L] do printf "  %.4o\t\t", l; end for;
            printf "\n";
        end for;
        "";

    end if;

until DPE ne 0;
