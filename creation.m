freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//                      Creation functions                        //
//                                                                //
////////////////////////////////////////////////////////////////////

// PSL2Z := PSL2(IntegerRing());

import "../ModSymA/core.m" : CosetReduce, ManinSymbolGenList;
import "misc.m" : NormalizerGrpMat;

intrinsic GetRealConjugate(H::GrpMat) -> GrpMat
{Returns a conjugate group in GL(N) that is of real type. (conjugated by [1,0,0,-1])}
  GL_N := GL(2, BaseRing(H));
  N_H := NormalizerGrpMat(GL_N, H);
  N_H_conjs := Conjugates(GL_N, N_H);
  eta := GL_N![-1,0,0,1];
  real := exists(real_N_H){ real_N_H : real_N_H in N_H_conjs
			    | eta in real_N_H};
  error if not real, Error("No real type conjugate");
  dummy, alpha := IsConjugate(GL_N,N_H,real_N_H);
  real_H := H^alpha;
  assert real_H^eta eq real_H;
  return real_H; 
end intrinsic;

// update, 3rd Sept 2002: changed order in which
// generators of SL2(Z) are given, to be compatible
// with functions for computing words for matrices
// in terms of T=[1,1,0,1] and S=[0,-1,1,0],
// as used in the intersection_pairing modular symbols file.

function init_psl2_group(N,R) 
    /* The basic internal creation function. */
    G := New(GrpGL2Hat);
    // warning!  Need to check for which
    // rings GL(2,R) works or not!!!
    if (Type(R) in {Rng,RngInt,FldRat}) then 
       G`MatrixGroup := GL(2,R);
    else
       G`MatrixGroup := MatrixAlgebra(R,2);
    end if;
    G`BaseRing := R;
    G`Level := N;
    G`conjugate_list := [GL(2,R)!1];
    G`IsNormalizer := false;
    G`IsOfGammaType := true;
    G`IsReal := true;
    return G;
end function;

function init_psl2_group_char(N,R,char) 
    G := init_psl2_group(N,R);
    G`character_list := [char];
    return G;
end function;

declare attributes Rng: StorePSL2;
 
intrinsic PSL2(R::Rng) -> GrpGL2Hat
    {The projective special linear matrix group PSL(2,R).}
    require Type(R) in {RngInt, FldRat, FldQuad, FldNum, FldRe}: 
           "The Argument must have type RngInt, FldRat, FldQuad, or FldRe";
    require not R cmpeq ComplexField(): "The Argument must be contained in the reals";
    if Type(R) eq FldQuad then
	require Discriminant(R) gt 0: "The Argument must be a ring contained in the reals";
    end if;

    if assigned R`StorePSL2 then
	return R`StorePSL2;
    end if;
//"GET PSL2 HARD:", R;

    G := init_psl2_group(1,R);
    G`BaseRing := R;
    G`Level := 1;
    G`IsOfGammaType := true;
    G`IsReal := true;
    G`gammaType_list:=[[1,1,1]];
    if Type(R) eq RngInt then
       T := G![1,1,0,1];
       S := G![0,1,-1,0];
       G`Generators := [T,S];
    end if;
    G`conjugate_list:=[GL(2,R)!1];

    R`StorePSL2 := G;
    return G;
end intrinsic;

intrinsic CongruenceSubgroup(A::SeqEnum) -> GrpGL2Hat
    {Given A = [n,m,p], this returns
    the congruence subgroup consisting of 2 by 2 matrices
    with integer coefficients [a,b,c,d]
    with a = d = 1 mod m,
    b = 0 mod p, and c = 0 mod n}
    require Universe(A) eq Integers() and #A eq 3
            and &and[A[i] ge 1 : i in [1..3]]: 
           "Please provide a list of 3 positive integers";
    n,m,p := Explode(A);
    require ((n*p) mod m) eq 0 :
            "The Argument must be a sequence N of 3 integers "
           * "with N[2] dividing N[1]*N[3]";
    N := Lcm(A);
    G := init_psl2_group(N,IntegerRing());
    G`gammaType_list := [A];
    return G;
end intrinsic;

intrinsic CongruenceSubgroup(A::SeqEnum,char::GrpDrchElt) -> GrpGL2Hat
    {Given N = [n,m,p], this returns
    the congruence subgroup consisting of 2 by 2 matrices
    with integer coefficients [a,b,c,d]
    with  b = 0 mod p, and c = 0 mod n, and char(a) = 1
    for char a Dirichlet character mod m}
    require Type(char) eq GrpDrchElt: "second argument must be a Dirichlet character";
    require A[2] mod Conductor(char) eq 0: 
      "The second argument must be a Dirichlet character with conductor dividing A[2]";    
    A[2] := Conductor(char);
    require char(-1) eq 1 : "Please give a character chi satisfying chi(-1) = 1";
    G := CongruenceSubgroup(A);
    subgroup_list_required := A[2] ne 1;  
    // Also not required if kernel(char) eq {1,-1} :
    if Order(Parent(char)) div Order(char) in {1,2} then 
        subgroup_list_required := false; end if;
    if subgroup_list_required then G`subgroup_list := [char]; end if;
    return G;
end intrinsic;

intrinsic CongruenceSubgroup(k::RngIntElt,N::RngIntElt) -> GrpGL2Hat
    {The congruence subgroup 
    Gamma_0(N), Gamma_1(N), Gamma(N), Gamma^1(N), or Gamma^0(N),
    when k = 0,1,2,3, or 4  respectively.}
    if k notin {0,1,2,3,4} then
	error "First argument must in {0,1,2,3,4}";
    end if;
    if N lt 1 then
	error "Second argument must be a positive integer";
    end if;
    if N eq 1 then
	return PSL2(Integers());
    end if;
    case k:
	when 0:
	return CongruenceSubgroup([N,1,1]);
	when 1:
	return CongruenceSubgroup([N,N,1]);
	when 2:
	return CongruenceSubgroup([N,N,N]);
	when 3:
	return CongruenceSubgroup([1,N,N]);
	when 4:
	return CongruenceSubgroup([1,1,N]);
    end case;
end intrinsic;

intrinsic CongruenceSubgroup(N::RngIntElt) -> GrpGL2Hat
   {The full projective congruence subgroup Gamma(N).}
   return CongruenceSubgroup(2,N);
end intrinsic;


//////////////////////////////////////////////////////////
//                                                      //
//  creation of special congruence subgroups            //
//                                                      //
//////////////////////////////////////////////////////////


intrinsic Gamma0(N::RngIntElt) -> GrpGL2Hat
    {creates the congruence subgroup Gamma_0(N)}
    require N gt 0: "Argument must be a positive integer";
    G := CongruenceSubgroup([N,1,1]);    
    return G;
end intrinsic;

intrinsic Gamma1(N::RngIntElt) -> GrpGL2Hat
   {creates the congruence subgroup Gamma_1(N)}
   require N gt 0: "Argument must be a positive integer";
    G := CongruenceSubgroup([N,N,1]);    
    return G;
 end intrinsic;


intrinsic GammaUpper0(N::RngIntElt) -> GrpGL2Hat
    {creates the congruence subgroup Gamma^0(N)}
    require N gt 0: "Argument must be a positive integer";
    G := CongruenceSubgroup([1,1,N]);    
    return G;
end intrinsic;

intrinsic GammaUpper1(N::RngIntElt) -> GrpGL2Hat
   {creates the congruence subgroup Gamma^1(N)}
   require N gt 0: "Argument must be a positive integer";
    G := CongruenceSubgroup([1,N,N]);    
    return G;
end intrinsic;

intrinsic GammaS(N::RngIntElt) -> GrpGL2Hat
{creates the congruence subgroup Gamma_s(N) which is split at all primes dividing N}
  Z_N := Integers(N);
  U, psi := UnitGroup(Z_N);
  gens := [psi(u) : u in Generators(U)];
  mat_gens := [[g,0,0,1] : g in gens] cat [[1,0,0,g] : g in gens];
  G_N := GL(2, Integers(N));
  C_N := sub<G_N | mat_gens>;
  G := PSL2Subgroup(C_N);
  G`Label := Sprintf("Gamma_s(%o)", N);
  G`IsReal := true;
  return G;
end intrinsic;

intrinsic GammaNS(N::RngIntElt, f::RngUPolElt[RngInt]) -> GrpGL2Hat
{creates the congruence subgroup Gamma_ns(N), choosing alpha as the root of the polynomial f, which should be irreducible modulo each prime dividing N. Currently supports only the case where ZZ[alpha] is a maximal order, where alpha is a root of f.}
   require N gt 0 : "N must be a positive integer";
   
   primes := [x[1] : x in Factorization(N)];
    
   for p in primes do
     Fp_x := PolynomialRing(Integers(p));
     require IsIrreducible(Fp_x!f) :
             "f must be irreducible mod every prime dividing N";
   end for;

   F := ext<Rationals() | f>;
   alpha := F.1;
   assert Evaluate(f,alpha) eq 0;
   R := Order([1,alpha]);
   // This is needed for Magma to be able to compute the unit groups
   // !!! problem : this is not always maximal
   // We want to use the generators for fast generation of the group
   require IsMaximal(R): "N for which ZZ[alpha] is not a maximal order 
   	   		 are not supported at the moment";
   pi_1 := hom< R -> Integers() | [1,0]>;
   pi_2 := hom< R -> Integers() | [0,1]>;
   NR := ideal<R | N>;
   A, phi := quo< R | NR>;
   // This is the non-split Cartan group abstractly
   U, psi := UnitGroup(A);
   // These are the generators under the regular representations
   gens := [[psi(u)*A![1,0],psi(u)*A![0,1]] : u in Generators(U)];
   // Same, only as matrices
   mat_gens := [Transpose(Matrix([[pi_1(g@@phi), pi_2(g@@phi)] : g in gen])) :
			gen in gens];
   G_N := GL(2, IntegerRing(N));
   C_N := sub<G_N | mat_gens>;
   G := PSL2Subgroup(C_N);
   G`Label := Sprintf("Gamma_ns(%o)", N);
   G`IsReal := true;
   G`NSCartanU := -Evaluate(f,0);
   G`NSCartanV := Coefficient(f,1);
   G`IsNSCartan := true;
   return G;
end intrinsic;


intrinsic GammaNS(N::RngIntElt, u::RngIntResElt) -> GrpGL2Hat
{creates the congruence subgroup Gamma_ns(N), choosing u as the nonsquare
    such that N | a-d, N | b-uc}
  require N gt 0: "N must be a positive integer";
  require Modulus(Parent(u)) eq N: "u must be a mod N residue";
  if not IsPrime(N) then
      ZZ_X<X> := PolynomialRing(Integers());
      u_lift := ChineseRemainderTheorem([3,Integers()!u], [4, N]);
      f := X^2 - u_lift;
      return GammaNS(N, f);
  end if;				       
  primes := [x[1] : x in Factorization(N)];
  good_u := &and[not IsSquare(IntegerRing(p)!u) : p in primes | p ne 2];
  require good_u: "u must be a nonsquare mod every prime dividing N";
  G_N := GL(2, IntegerRing(N));
  // currently assumes N=p is prime
  // In general will have to consider arbitrary irreducibles
  F := GF(N);
  // TODO : Treat the general case for N 
  if N eq 2 then
    C_N := sub<G_N | [0,1,1,1]>; 
  else
    F2<t> := ExtensionField<F,t | t^2-F!u>;
    zeta := PrimitiveElement(F2);
    a := F!((zeta + Frobenius(zeta))/2);
    b := F!((zeta - Frobenius(zeta))/(2*t));
    g := [a,F!u*b,b,a];
    C_N := sub<G_N | [IntegerRing(N)!x : x in g]>;
  end if;
  G := PSL2Subgroup(C_N);
  G`Label := Sprintf("Gamma_ns(%o)", N);
  G`IsReal := true;
  G`NSCartanU := u;
  G`NSCartanV := 0;
  G`IsNSCartan := true;
  return G;
end intrinsic;

intrinsic GammaNS(N::RngIntElt) -> GrpGL2Hat
{creates the congruence subgroup Gamma_ns(N)}
   if IsPrime(N) then
       return GammaNS(N, Integers(N)!Nonsquare(GF(N)));
   end if;
   primes := [x[1] : x in Factorization(N)];
   ZZ_x<x> := PolynomialRing(Integers());
   if 2 in primes then
       primes := [p : p in primes | p ne 2];
       crt_vals := [5] cat [Integers()!Nonsquare(GF(p)) :
			    p in primes];
       y := ChineseRemainderTheorem(crt_vals, [8] cat primes);
       v := (1-y) div 4;   
       return GammaNS(N, x^2 + x + v);
   else
       // we take primitive elements for the quadratic order to be maximal,
       // That way magma can handle it better, even though it is not truly necessary.
       crt_vals := [3] cat [Integers()!PrimitiveElement(GF(p)) : p in primes];
       u := ChineseRemainderTheorem(crt_vals, [4] cat primes);
       return GammaNS(N, x^2 - u);
   end if;
//   u := PrimitiveElement(IntegerRing(N));
end intrinsic;

intrinsic GammaSplus(N::RngIntElt) -> GrpGL2Hat
{creates the congruence subgroup Gamma_s^plus(N)}
   return Normalizer(GammaS(N));
end intrinsic;

intrinsic GammaNSplus(N::RngIntElt, u::RngIntResElt) -> GrpGL2Hat
{creates the congruence subgroup Gamma_ns^plus(N)}
   return Normalizer(GammaNS(N,u));
end intrinsic;

intrinsic GammaNSplus(N::RngIntElt) -> GrpGL2Hat
{creates the congruence subgroup Gamma_ns^plus(N)}
   return Normalizer(GammaNS(N));
end intrinsic;

intrinsic GammaShimura(U::GrpAb, phi::Map,
		       H::GrpAb, t::RngIntElt) -> GrpGL2Hat
{creates the congruence subgroup Gamma(H,t), defined by Shimura.
    H is a subgroup of UnitGroup(ZZ / N ZZ), and t divides N.
    These are matrices such that modulo N they are upper triangular,
    the diagonal elements are in H, and the upper right element is
    a multiple of t.}
   N := Modulus(Codomain(phi));
   h_gens := [phi(g) : g in Generators(H)];
   all_gens := [phi(g) : g in Generators(U)];           
   mat_gens := [[-1,0,0,-1],[1,t,0,1]] cat [[a,0,0,1] : a in h_gens]
		cat [[1,0,0,d] : d in all_gens];
   return PSL2Subgroup(sub<GL(2, Integers(N)) | mat_gens>);
end intrinsic;

function my_Gamma(N, type)
  if N eq 1 then
     // just take en entire GL(2,N) for some N
    return PSL2Subgroup(GL(2,IntegerRing(2)), false);
  end if;
  Z_N := IntegerRing(N);
  G_N := GL(2, Z_N);
  // gens := [-G_N!1];
  gens := [];
  U, psi := UnitGroup(Z_N);
  // This matches our convention for the Galois action
  for t in Generators(U) do
    Append(~gens, G_N![1,0,0,psi(t)]);
  end for;
  if Type(type) eq RngIntElt then
     Append(~gens, G_N![1,1,0,1]);   
     if type eq 0 then
       for t in Generators(U) do
	 Append(~gens, G_N![psi(t),0,0,1]);
       end for;
     end if;
  end if;
  H_N := sub<G_N | gens>;
  return PSL2Subgroup(H_N, true);
end function;

intrinsic FakeGamma(N::RngIntElt, type::RngIntElt) -> GrpPSL2
{Creates a congruence subgroup of gamma type, for testing.}
  return my_Gamma(N, type);
end intrinsic;

intrinsic FakeGamma(N::RngIntElt, type::MonStgElt) -> GrpPSL2
{Creates a congruence subgroup of gamma type, for testing.}
  return my_Gamma(N, type);
end intrinsic;

// Creation of Quotient

intrinsic '/'(G::GrpGL2Hat, H::GrpGL2Hat) -> GrpGL2Hat
	     {Currently assumes the same level.}

//   require ModLevelGL(G) eq ModLevelGL(H) :
//          "the groups must be of the same level";

   level := LCM(Level(G), Level(H));
   return ImageInLevelGL(G : N := level)/ImageInLevelGL(H : N := level);
/*
   require ModLevel(G) eq ModLevel(H) :
          "the groups must be of the same level";
   return ImageInLevel(G)/ImageInLevel(H);
*/
end intrinsic;

intrinsic Transversal(G::GrpGL2Hat, H::GrpGL2Hat) -> GrpGL2Hat
{Return coset representatives for H\G}
  require H subset G : "argument 2 must a subgroup of argument 1.";
  im_G := ImageInLevel(G : N := Level(H));
  im_H := ImageInLevel(H);
  return [PSL2(Integers()) | FindLiftToSL2(x) : x in Transversal(im_G, im_H)];
end intrinsic;

//////////////////////////////////////////////////////////
//                                                      //
//  creation of normalizer of G                         //
//                                                      //
//////////////////////////////////////////////////////////

intrinsic Normalizer(G::GrpGL2Hat) -> GrpGL2Hat
   {The normalizer of a congruence subgroup in SL_2(R)}
   // require IsGamma0(G): "the argument must be Gamma_0(N) for some integer N";
   if Level(G) eq 1 then return G; end if;
   if IsGamma0(G) then
     H := init_psl2_group(Level(G),Integers());
     N := Level(G);
     H`gammaType_list := [[N,1,1]]; 
     F := Factorization(N);
     r := #F;
     H`LevelFactorization := F;
     H`AtkinLehnerInvolutions := VectorSpace(FiniteField(2),r);
   else     
     N_G := NormalizerGrpMat(ModLevelGL(G), ImageInLevelGL(G));
     H := PSL2Subgroup(N_G, true);
   end if;
   H`IsNormalizer := true;
   H`Label := Sprintf("Normalizer in PSL_2(%o) of ", G`BaseRing) cat Label(G);
   if IsOfRealType(G) then H`IsReal := true; end if;
   if IsGammaNS(G) or IsGammaNSplus(G) then
       H`NSCartanU := G`NSCartanU;
       H`NSCartanV := G`NSCartanV;
     H`IsNSCartan := false;
     H`IsNSCartanPlus := true;
   end if;
   return H;
end intrinsic;

intrinsic MaximalNormalizingWithAbelianQuotient(G_prime::GrpMat,
						G::GrpMat,
						H::GrpMat : RealType := true) -> GrpMat
{}
    N_G := NormalizerGrpMat(G_prime, G);
    require H subset N_G : "H must normalize G";
    Q, pi_Q := N_G / G;
    H_im := H@pi_Q;
    require IsAbelian(H_im) : "HG/G must be Abelian";
    // At the moment, magma cannot compute irreducible modules for
    // non soluble groups over characteristic 0 fields
    // if (not IsSoluble(Q)) or (#Q eq 1) then
    // In fact, if Q is not nilpotent,
    // currently don't know how to find maximal abelian subgroups
    if IsAbelian(Q) then
	return N_G;
/* In this case it might not work, but it is worth a try
    elif not IsNilpotent(Q) then
       return H;
*/
    else
      // find a maximal abelian subgroup containing H
      A := sub<Q | Center(Q), H_im>;
      C := Centralizer(Q,A);
      while (C ne A) do
	gens := Generators(C);
        for g in gens do
	  if g notin A then
	    A := sub<Q|A,g>;
            break;
          end if;
        end for;
        C := Centralizer(Q,A);
      end while;
    end if;
    A_pre := A @@ pi_Q;
    if RealType then
	// We force the normalizing group to be of real type.
	eta := G_prime![-1,0,0,1];
	A_pre := A_pre meet A_pre^eta;
	assert A_pre^eta eq A_pre;
    end if;
    return A_pre;
end intrinsic;

intrinsic MaximalNormalizingWithAbelianQuotient(G::GrpGL2Hat) -> GrpGL2Hat
{}
    if Level(G) eq 1 then return G; end if;
    im_G  := ImageInLevelGL(G);
    G_prime := MaximalNormalizingWithAbelianQuotient(ModLevelGL(G),
						     im_G, im_G);
    H := PSL2Subgroup(G_prime, true);
    H`Label := Sprintf("Maximal Abelian Subgroup of Normalizer in 
                        PSL_2(%o) of ", G`BaseRing) cat Label(G);
    if IsOfRealType(G) then H`IsReal := true; end if;
    if IsGammaNS(G) or IsGammaNSplus(G) then
	H`NSCartanU := G`NSCartanU;
	H`NSCartanV := G`NSCartanV;
      H`IsNSCartan := false;
      H`IsNSCartanPlus := true;
    end if;
    H`DetRep := G`DetRep;
    return H;
end intrinsic;

//////////////////////////////////////////////////////////
//                                                      //
//  creation of random elements of congruence subgroups //
//                                                      //
//////////////////////////////////////////////////////////


intrinsic Random(G::GrpGL2Hat,m::RngIntElt) -> GrpGL2HatElt
    {returns a random element of the projective linear group G,
    m determines the size of the coefficients}    
    // assume the group is congruence, given by [N,M,P]
    N,M,P := Explode(G`gammaType_list[1]);
    limN := Ceiling(m/N);
    limM := Ceiling(m/M);
    limP := Ceiling(m/P);

    g := 0;
    while g ne 1 do
    c := Random(-limN,limN)*N;
    d := Random(-limM,limM)*M + 1;
    b := Random(-limP,limP)*P;
	g, r,a := Xgcd(-c*b,d);
    end while;
    // b and c have been lumped together;
    // so have to change r to r*b, and c*b to c, so that
    // r*b, a = Xgcd(-c,d) :
    b := r*b;
    // matrix [a,b,c,d] is OK, but would like to
    // have top coeffs, a,b as close as possible to
    // requested range, so need to add a multiple of
    // bottom row to top row.
    // WARNING : the following is not quite right yet!
    fac1 := M div Gcd(M,N);
    fac2 := P div Gcd(P,d);
    mul := Lcm(fac1,fac2);
    if c gt 0 then
	lims1 := [-Floor((a+m)/mul/c),Floor((m-a)/mul/c)];
    elif c lt 0 then
	lims1 := [-Floor((m-a)/mul/c),Floor(-(m+a)/mul/c)];
    else lims1 := [0,0];
    end if;
    if d gt 0 then
	lims2 := [-Floor((b+m)/mul/d),Floor((m-b)/mul/d)];
    elif d lt 0 then
	lims2 := [-Floor((m-b)/mul/d),Floor(-(m+b)/mul/d)];
    else lims2 := [0,0];
    end if;

    lims := [Max(lims1[1],lims2[1]),Min(lims1[2],lims2[2])];
    if lims[2] lt lims[1] then
	t := 0;
    else
	t := Random([lims[1],lims[2]]);
    end if;
    
    g := G![a + mul*c*t,b + mul*d*t,c,d];    
    return g;
end intrinsic;



//////////////////////////////////////////////////////////
//                                                      //
//      Methods of obtaining new congruence subgroups:  //
//  conjugation and intersetcion                        //
//                                                      //
//////////////////////////////////////////////////////////

function slow_conjugate(G, A, IsExactLevel)
  gens := Generators(G);
  det := Integers()!Determinant(A);
  H_gens := [];
  for g in gens do
      elt := A^(-1) * GL(2,Rationals())!Eltseq(g) * A;
      new_g := PSL2(Integers())!Eltseq(elt);
      Append(~H_gens, new_g);
  end for;
  gens_level := [Eltseq(h) : h in H_gens];// cat [[-1,0,0,-1]];
  mod_level := ModLevel(G);
  mod_level := SL(2, Integers(Level(G) * det));
  im_in_level := sub<mod_level | gens_level >;
  return PSL2Subgroup(im_in_level, IsExactLevel);
end function;
  
// Faster than before, could still use improvements
// Perhaps compute level of conjugation a priori,
// by checking conjugating kernels
function fast_conjugate(G, A, IsExactLevel)
    N := Level(G);
    det := Integers()!Determinant(A);
    M2Z := MatrixAlgebra(Integers(),2);
    // notation from here on assumes det = p is prime
    GN := ImageInLevelGL(G);
    // GpN := ImageInLevelGL(G : N := det*N); 
    // The above line is slow. check why we are not simply lifting
    lifts := &cat[[M2Z!([N*eps[i] : i in [1..4]]) + M2Z!Matrix(g) : 
		   eps in CartesianPower([0..det^2-1],4)] : g in Generators(GN)];
    // !! TODO : Not sure that we really need det^2 here, check that

/*
"SUBG mod:", Factorization(det^2*N);
"#lifts:", #lifts;
lifts := Set(lifts);
"new #lifts:", #lifts;
//"lifts:", lifts;
time     GpN := sub<GL(2, Integers(det^2*N)) | lifts>;
"Get order:";
time #GpN;
*/

R := Integers(det^2*N);
//gl := GL(2, Integers(det^2*N));
//gl;
//Universe(lifts);
MR := MatrixRing(R, 2);
gens := {MR ! x: x in lifts};

    AmodpN := MatrixAlgebra(Integers(det^2*N),2)!A;
    Atilde_modpN := Adjoint(AmodpN);
    //gens := [Atilde_modpN*g*AmodpN : g in Generators(GpN)];
    gens := [Atilde_modpN*g*AmodpN : g in gens];
//    assert &and[&and[(Integers()!x) mod det eq 0  : x in Eltseq(g)] : g in gens];
    Z := Integers();
    lifts := [GL(2,Integers(det*N))!
		 [(Z!x) div det : x in Eltseq(g)] 
		 : g in gens];
    /*
    lifts := &cat[[M2Z!([N*eps[i] : i in [1..4]]) + M2Z!Matrix(g) : 
		   eps in CartesianPower([0..det-1],4)] : 
		  g in im_mod_N];
   */
    conj_mod_pN := sub<GL(2, Integers(det*N)) | lifts>;
    ret := PSL2Subgroup(conj_mod_pN, IsExactLevel);
    // Not equal because ret_slow only sees the PSL2 subgroup (det eq 1)
    // ret_slow := slow_conjugate(G, A, IsExactLevel);
    // assert ret eq ret_slow;
    return ret;
end function;

intrinsic Conjugate(G::GrpGL2Hat, A::GrpMatElt : IsExactLevel := false) -> GrpGL2Hat
{This function returns the conjugation of G by A, i.e. A^(-1)*G*A
     At the moment we only support the case where
     both input and output are subgroups of PSL2(Z)}
  if IsOne(A) then return G; end if;
  M2Z := MatrixAlgebra(Integers(),2);
  // reducing to an integral matrix
  D := Rationals()!LCM([Denominator(x) : x in Eltseq(A)]);
  A := ScalarMatrix(2,D) * A;
  det := Integers()!Determinant(A);

  if (G eq PSL2(Integers())) then
     return G;
  end if;
  if (A in Gamma0(1)) then
     return PSL2Subgroup(Conjugate(ImageInLevelGL(G),ModLevelGL(G)!A));		
  end if;

  N := Level(G);

  if GCD(det, N) eq 1 then
    AmodN := ModLevelGL(G)!A;
    mod_N := Conjugate(ImageInLevelGL(G), AmodN);
    snf, x, y := SmithForm(M2Z!A);
    quot := snf[2,2] div snf[1,1];
    y_mod := GL(2, Integers(det))!y;
    mod_det := Conjugate(ImageInLevelGL(GammaUpper0(quot) : N := det),
			 y_mod^(-1));
    gens_N := [[Integers()!y : y in Eltseq(x)] : x in Generators(mod_N)];
    gens_det := [[Integers()!y : y in Eltseq(x)] : x in Generators(mod_det)];
    one := [1,0,0,1];
    gens_1 := [[ChineseRemainderTheorem([g[i], one[i]], [N,det])
	       : i in [1..4]] : g in gens_N];
    gens_2 := [[ChineseRemainderTheorem([one[i], g[i]], [N,det])
	       : i in [1..4]] : g in gens_det];
    gens := gens_1 cat gens_2;
    H := sub<GL(2,Integers(N*det)) | gens>;
    return PSL2Subgroup(H, IsExactLevel);
  end if;

  // At the moment we always calculate generators
  // If they have not been calculated yet, can add later more efficient
  // methods
  // return slow_conjugate(G, A, IsExactLevel);
  return fast_conjugate(G, A, IsExactLevel);
end intrinsic;

intrinsic '^'(G::GrpGL2Hat, A::GrpMatElt) -> GrpGL2Hat
{}
  return Conjugate(G,A);
end intrinsic;

// sometimes G^A is not in GL_2(Zhat), but we still want to compute
// G^A meet G in GL_2(Zhat). The following intrinsic does that
intrinsic MeetConjugate(G::GrpGL2Hat, A::GrpMatElt) -> GrpGL2Hat
{}
   M2Z := MatrixAlgebra(Integers(),2);
   GL2Q := GL(2, Rationals());
   D := Rationals()!LCM([Denominator(x) : x in Eltseq(A^(-1))]);
   A_tilde := M2Z!(ScalarMatrix(2,D) * A^(-1));
   r , dummy , t := SmithForm(M2Z!A_tilde);
   gamma1_conj := GammaUpper0(r[2,2] div r[1,1]);

   gamma1_A_conj := Conjugate(gamma1_conj, GL2Q!t^(-1));

/*
  // verify that this is indeed the A*Gamma(1)*A^(-1) meet Gamma(1)
  gens := [GL2Q!Eltseq(g) : g in Generators(gamma1_A_conj)];
  assert &and[IsCoercible(M2Z,A^(-1)*g*A) : g in gens];
  assert Index(gamma1_A_conj) eq #gamma1_reps;
*/

   G_A_conj := Conjugate(G meet gamma1_A_conj, A);

/*
  // verify that this is contained in A^(-1)*G*A meet Gamma(1)
  // This suggests that here we don't have the full intersection
  gens := [GL2Q!Eltseq(g) : g in Generators(gamma_A_conj)];
  assert &and[A*g*A^(-1) in G : g in gens];
*/

  H := G meet G_A_conj;

/*
  // Check that H is contained in A^(-1)*G*A
  gens := [GL2Q!Eltseq(g) : g in Generators(H)];
  assert &and[A*g*A^(-1) in G : g in gens];
*/
  return H;
end intrinsic;

// This was the only way I could get the reduction morphism

function get_coercion_hom(G,H)
  if Degree(H) eq 1 then
    return hom<G -> H | [H!1 : i in [1..NumberOfGenerators(G)]]>;
  end if;
  return hom<G->H | [H!G.i : i in [1..NumberOfGenerators(G)]]>;
end function;

intrinsic Intersection(G::GrpGL2Hat,H::GrpGL2Hat) -> GrpGL2Hat
    {returns the intersection of two congruence subgroups.}

  require Type(G`BaseRing) eq RngInt : "G, H must be congruence subgroups";

  if G`IsOfGammaType and H`IsOfGammaType then
    conListG := G`conjugate_list;
    conListH := H`conjugate_list;
    require #conListG eq 1 and #conListH eq 1 and
    conListG[1] eq GL(2,G`BaseRing)!1 and
    conListH[1] eq GL(2,H`BaseRing)!1:
    "Not yet implemented for the
    groups you have entered";
    // initiate group
    // find the 3 integers giving group
    Hlist := (H`gammaType_list)[1];
    Glist := (G`gammaType_list)[1];
    A := [Lcm(Hlist[i],Glist[i]) : i in [1..3]];   
    K := init_psl2_group(Lcm(A),Integers());
    K`gammaType_list := [A];
    K`IsOfGammaType := true;
    return K;
  else
    N_G := Level(G);
    N_H := Level(H);
    d := GCD(N_G, N_H);
    N := LeastCommonMultiple(N_G, N_H);   
    if (Type(G`BaseRing) in {Rng,RngInt,FldRat}) then 
        ModLevelGL := GL(2,quo<G`BaseRing | N>);
    else
        ModLevelGL := MatrixAlgebra(quo<G`BaseRing | N>,2);
    end if;
    if (d eq 1) then
      target := GL(1, Integers(2));
    else
      target := GL(2, Integers(d));
    end if;
    red_G := get_coercion_hom(ImageInLevelGL(G), target);
red_H := get_coercion_hom(ImageInLevelGL(H), target);
    G_d := Kernel(red_G);
    H_d := Kernel(red_H);
    im_d := Image(red_G) meet Image(red_H);
    gens_G_d := [[Integers()!y : y in Eltseq(g)] : g in Generators(G_d)];
    gens_H_d := [[Integers()!y : y in Eltseq(g)] : g in Generators(H_d)];
    equalizer := [[* z@@red_G, z@@red_H *] : z in Generators(im_d)];
    gens_im_d := [[[Integers()!y : y in Eltseq(g)] : g in x] : x in equalizer];
    one := [1,0,0,1];
    gens_1 := [[ChineseRemainderTheorem([g[i], one[i]], [N_G,N_H])
	       : i in [1..4]] : g in gens_G_d];
    gens_2 := [[ChineseRemainderTheorem([one[i], g[i]], [N_G,N_H])
	       : i in [1..4]] : g in gens_H_d];
    gens_3 := [[ChineseRemainderTheorem([g[1][i], g[2][i]], [N_G,N_H])
	       : i in [1..4]] : g in gens_im_d];
    gens := gens_1 cat gens_2 cat gens_3;
    G_meet_H := sub< ModLevelGL | gens>;
    return PSL2Subgroup(G_meet_H, true);
/* old version:

    gens_G := [Eltseq(x) : x in Generators(G)];
    gens_H := [Eltseq(x) : x in Generators(H)];
    Append(~gens_G, [-1,0,0,-1]);
    Append(~gens_H, [-1,0,0,-1]);
    G_image := sub<ModLevel | gens_G>;
    H_image := sub<ModLevel | gens_H>;
    return PSL2Subgroup(G_image meet H_image);
*/
  end if;
end intrinsic;
 

intrinsic 'meet' (G::GrpGL2Hat,H::GrpGL2Hat) -> GrpGL2Hat
    {returns the intersection of two congruence subgroups.}
    return Intersection(G,H);
end intrinsic;

// This is not good enough -
// we want level as a GL2 subgroup

intrinsic CalcLevel(G::GrpGL2Hat) -> RngIntElt
{calculates the level of a subgroup of PSL2}
  if Degree(ModLevel(G)) eq 1 then return 1; end if;
  mlist := ManinSymbolGenList(2,G,G`BaseRing);
  coset_list := mlist`coset_list;
  find_coset := mlist`find_coset;
  T := ModLevel(G) ! [1,1,0,1];
  T_map := [CosetReduce(ModLevel(G)!Matrix(x) * T,
		      find_coset) : x in coset_list];
  perm_T := SymmetricGroup(#T_map)!T_map;
  min_level := Order(perm_T);
  max_level := Modulus(BaseRing(ModLevel(G)));
  cur_level := max_level;
  found := true;
  while (cur_level gt min_level) and found do
    primes := [x[1] : x in Factorization(cur_level)];
    found := false;
    bigG := GL(2, Integers(cur_level));
    for p in primes do
      level := cur_level div p;
      imG := sub< bigG | Generators(ImageInLevelGL(G))>;
      if level eq 1 then
        contains_ker := bigG subset imG;
      else
        lifts := [bigG !
	      [1 + level*a, level*b, level*c, 1+level*d]
		     : a,b,c,d in [0..p - 1]
		    | GCD((1+level*a)*(1+level*d)-level^2*(b*c),
			  cur_level) eq 1];
        contains_ker := &and[lift in imG : lift in lifts];
      end if;
      if contains_ker then
        cur_level := level;
        found := true;
        break;
      end if;
    end for;
  end while; 
  return cur_level;
end intrinsic;

 // Eventually we would like to compute the level and check
 // whether it is a congruence subgroup ourselves
 
intrinsic SubgroupFromGens(G::GrpGL2Hat, gens::SeqEnum, N::RngIntElt,
			   IsExactLevel::BoolElt) -> GrpGL2Hat
     {returns the subgroup of G generated by gens.}
     H := New(GrpGL2Hat);
     H`MatrixGroup := G`MatrixGroup;
     H`BaseRing := G`BaseRing;
     H`IsOfGammaType := false;
     H`Generators := gens;
     if (Type(H`BaseRing) in {Rng,RngInt,FldRat}) then 
        H`ModLevel := SL(2,quo<H`BaseRing | N>);
     else
        H`ModLevel := MatrixAlgebra(quo<H`BaseRing | N>,2);
     end if;
     H`ImageInLevel := sub< H`ModLevel | [H`ModLevel!Matrix(g) : g in gens]>;
     H`Level := N;
     if not IsExactLevel then
       H`Level := CalcLevel(H);
     end if;
     return H;
end intrinsic;

intrinsic PSL2SubgroupFromGens(gens::SeqEnum, R::Rng, N::RngIntElt,
			       IsExactLevel::BoolElt) -> GrpGL2Hat
     {returns the subgroup of PSL2(R) generated by gens}
    return SubgroupFromGens(PSL2(R), gens, N, IsExactLevel);
end intrinsic;

// Lift an element of SL2(Z/NZ) to an element of SL2(Z)
 
intrinsic FindLiftToSL2(g::GrpMatElt) -> GrpGL2HatElt
{finds a lift in SL2 for g}
     elt_g := ElementToSequence(g);
     if #elt_g eq 1 then return PSL2(Integers())!1; end if;
     a,b,c,d := Explode(elt_g); 
     N := Modulus(Parent(a));
     Z := Integers();
     a_prime := Z!a;
     b_prime := Z!b;
     if a_prime eq 0 then
        a_prime +:= N;
     end if;
     gcd_res, x, y := Xgcd(a_prime, b_prime);
     while gcd_res ne 1 do
           b_prime +:= N; 
           gcd_res, x, y := Xgcd(a_prime, b_prime);
     end while;
     det := a_prime * Z!d - b_prime*Z!c;
     c_prime := Z!c - y * (1 - det);
     d_prime := Z!d + x * (1 - det);       
//lift_g := SL(2,Z)![a_prime, b_prime, c_prime, d_prime];
     lift_g := PSL2(Integers())![a_prime, b_prime, c_prime, d_prime];
     return lift_g;
end intrinsic;

// For now assume det is either 1 or a prime
intrinsic FindLiftToM2Z(g::AlgMatElt[RngIntRes] : det := 1) -> AlgMatElt[RngInt]
{finds a lift in M2Z for g}
     require g ne 0 : "Can not find lift for the zero matrix!";
     M2Z := MatrixAlgebra(Integers(), 2);
     elt_g := ElementToSequence(g);
     if #elt_g eq 1 then return PSL2(Integers())!1; end if;
     a,b,c,d := Explode(elt_g); 
     N := Modulus(Parent(a));
     Z := Integers();
     a_prime := Z!a;
     b_prime := Z!b;
     if a_prime eq 0 then
        a_prime +:= N;
     end if;
     gcd_res, x, y := Xgcd(a_prime, b_prime);
     if GCD(gcd_res, det) ne 1 then
       rev := FindLiftToM2Z(Parent(g)![d,c,b,a] : det := det);
       d_prime,c_prime,b_prime,a_prime := Explode(Eltseq(rev));
       return M2Z![a_prime, b_prime, c_prime, d_prime];
     end if;
     while gcd_res ne 1 do
        b_prime +:= N; 
        gcd_res, x, y := Xgcd(a_prime, b_prime);
     end while;
     det_prime := a_prime * Z!d - b_prime*Z!c;
     mult := det - det_prime;
     c_prime := Z!c - y * mult;
     d_prime := Z!d + x * mult;
     lift_g := M2Z![a_prime, b_prime, c_prime, d_prime];
     return lift_g;
end intrinsic;

function get_mod_level(H, N)
     if N eq 1 then
       dim := 1;
       level := 2;
     else
       dim := 2;
       level := N;
     end if;
     is_gl := (Type(H`BaseRing) in {Rng,RngInt,FldRat});
     if is_gl then 
        ModLevel := SL(dim, quo<H`BaseRing | level>);
        ModLevelGL := GL(dim, quo<H`BaseRing | level>);
     else
        ModLevel := MatrixAlgebra(quo<H`BaseRing | level>, dim);
        ModLevelGL := MatrixAlgebra(quo<H`BaseRing | level>, dim);
     end if;
     return ModLevel, ModLevelGL;
end function;

intrinsic SubgroupFromMod(G::GrpGL2Hat, N::RngIntElt, H0::GrpMat,
			  IsExactLevel::BoolElt : CosetReps := [], FindCoset := false) -> GrpGL2Hat
{returns the subgroup of G generated whose image is H0.}

//"RUN SubgroupFromMod"; "G:", G; TES(G);

     H := New(GrpGL2Hat);
     H`MatrixGroup := G`MatrixGroup;
     H`BaseRing := G`BaseRing;
     H`IsOfGammaType := false;
     H`ModLevel, H`ModLevelGL := get_mod_level(H, N);
     if N eq 1 then
	 H`ImageInLevel := H`ModLevel;
	 H`ImageInLevelGL := H`ModLevelGL;
     else
	 // H`ImageInLevel := H0 meet H`ModLevel;
	 // Computing the kernel of the determinant map seems to be slightly faster

// "H0 mag:", H0: Magma;

	 if Ngens(H0) gt 1 then
	     gl := Generic(H0);
	     gens := Generators(H0);
	     k := 3;
	     repeat
		HH:=sub<gl|[Random(gens): i in [1..k]]>;
		k +:= 1;
	     until forall{h: h in gens | h in HH};
	     H0 := HH;
	 end if;

//"Smaller H0:", H0;

	 gl1 := GL(1, Integers(N));
//"H0:", H0;
//"gl1:", gl1;
//"rhs im:", [gl1![[Determinant(H0.i)]]: i in [1..Ngens(H0)]];
//"Get hom"; time
	 det_hom := hom<H0 -> gl1 | [gl1![[Determinant(H0.i)]]: i in [1..Ngens(H0)]]>;
//"Get ker"; time
	 H`ImageInLevel := Kernel(det_hom);
//"GOT ker:", H`ImageInLevel;
	 H`ImageInLevelGL := H0;
     end if;
     H`Level := N;

/*
"HERE H`Level:", H`Level;
"HERE H`ModLevel:", #H`ModLevel;
"Base Ring:", BaseRing(H`ModLevel);
"HERE H`ImageInLevelGL:", #H`ImageInLevelGL;
"HERE H`ImageInLevel:", #H`ImageInLevel;
"HERE quot:", #H`ImageInLevelGL / #H`ImageInLevel;
*/

     cosets, find_coset := Transversal(H`ModLevel, H`ImageInLevel);
     // Drew suggested that computing the transversal in GL_2 would be faster
     // when the determinant is surjective, but tests seem to indicate differently.
     // Should see if we can postpone computing these until they are needed.
     if IsEmpty(CosetReps) then
	 cosets, find_coset := Transversal(H`ModLevel, H`ImageInLevel);
     else
	 cosets := CosetReps;
	 find_coset := FindCoset;
     end if;
     if N eq 1 then
	 H`FS_cosets := [G!1];
     else
	 if (-H0!1 notin H0) then
	     psl_image := sub<H`ModLevel | H`ImageInLevel, [-1,0,0,-1]>;
	     pcosets, _ := Transversal(H`ModLevel, psl_image);
	 else
	     psl_image := H`ImageInLevel;
	     pcosets := cosets;
	 end if;
	 H`FS_cosets := [G | FindLiftToSL2(find_coset(c)) : c in pcosets];
     end if;

    codom := [<i, cosets[i]^(-1)> : i in [1..#cosets]];
    if 1 eq 1 then
        A := AssociativeArray();
        for i in [1..#cosets] do
            A[cosets[i]] := codom[i];
        end for;
        coset_idx := map<cosets -> Universe(codom) | x :-> A[x]>;
    else
        coset_idx := map<cosets -> codom |
           [<cosets[i], codom[i] > : i in [1..#cosets]] >;
    end if;

    HH := H`ModLevel;

    m := find_coset*coset_idx;

om := m;
//"om:", om; "om CODOM:", Codomain(om);

INFO := 0 eq 1;

    if 1 eq 1 then
	if #HH le 10^5 then
	    A := AssociativeArray();
	    if INFO then
		"[";
		IndentPush();
		printf "SubgroupFromMod (L %o): USE Assoc for HH of order %o\n",
		    #BaseRing(HH), #HH;
		time for h in HH do
		    A[h] := m(h);
		end for;
	    else
		for h in HH do
		    A[h] := m(h);
		end for;
	    end if;
	    if INFO then
		IndentPop();
		"]";
	    end if;
	    m := map<(HH) -> Universe(codom) | x :-> A[x]>;
	    //m := map<(HH) -> (codom) | x :-> A[x]>;
	else
	    if INFO then
	      printf "SubgroupFromMod (L %o): SKIP Assoc for HH of order %o\n",
		    #BaseRing(HH), #HH;
	    end if;
	end if;
    end if;
//"new m:", m; "new m CODOM:", Codomain(m);

//assert Codomain(m) eq Codomain(om);

//"om IMAGE:", Image(om); "m IMAGE:", Image(om);

     H`FindCoset := om;
     H`FindCosetQ := m;

//"SET H`FindCoset:", H`FindCoset;

     // In the case N eq 1, we leave it as it was - coudl an dshould do better but not now
     if (N eq 1) then
	 det_cosets := Transversal(H0, H`ImageInLevel);
	 dom := [Determinant(x) : x in det_cosets];
	 H`DetRep := map< dom -> H0 | [<Determinant(x),x> : x in det_cosets] >;
     else
	 det_cosets := Image(det_hom);
	 dom := [x[1,1] : x in det_cosets];
	 H`DetRep := map< dom -> H0 | [<x[1,1],x@@det_hom> : x in det_cosets] >;
     end if;
     if IsExactLevel then
        H`Level := N;
     else
        H`Level := CalcLevel(H);
        H`ModLevel, H`ModLevelGL := get_mod_level(H, H`Level);
        if H`Level eq 1 then
	  H0bar := H`ModLevelGL;
        else
          H0bar := sub<H`ModLevelGL | Generators(H0) >;
        end if;
        return SubgroupFromMod(G, H`Level, H0bar, true);
     end if;
     return H;
end intrinsic;

DO_STORE := 1 eq 1;

declare attributes Rng: A;
Z := IntegerRing();
GET_STORE := func< | Z>;
STORE := GET_STORE();
STORE`A := AssociativeArray();

intrinsic PSL2Subgroup(H::GrpMat, IsExactLevel::BoolElt : CosetReps := [], FindCoset := false) -> GrpGL2Hat
 {returns a subgroup of PSL2(Z) whose image is H (assumes -I in H)}

 /*
 "CALL PSL2Subgroup";
 H: Minimal;
 "TES(H):"; TES(H);
 "Hash gens:", Hash(Generators(H));
 //Traceback();
 */

    if DO_STORE then
	STORE := GET_STORE();
	A := STORE`A;
	g := {Matrix(Z, x): x in Generators(H)};
	t := < #BaseRing(H), Hash(g), g >;
//if #A gt 0 then "UNIV:", Universe(A); end if; "HERE t:", t;
	if IsDefined(A, t) then
//"   REUSE";
	    return A[t];
	end if;
    end if;

     require Type(BaseRing(H)) eq RngIntRes : "Image group must be Z/NZ";
     if Dimension(H) eq 1 then
	 return Gamma0(1);
     end if;
     require Dimension(H) eq 2 : "Group must be of 2x2 matrices";
     // This check takes too long to verify
     // require GL(2,BaseRing(H))![-1,0,0,-1] in H : "Currently assume -I in H";
     N := Modulus(BaseRing(H));   

     S := SubgroupFromMod(PSL2(Integers()), N, H, IsExactLevel : CosetReps := CosetReps, FindCoset := FindCoset);

    if DO_STORE then
	STORE`A := 0;
	A[t] := S;
	STORE`A := A;
    end if;

     return S;
end intrinsic;

intrinsic PSL2Subgroup(H::GrpMat: CosetReps := [], FindCoset := false) -> GrpGL2Hat
 {returns a subgroup of PSL2(Z) whose image is H (assumes -I in H)}
   return PSL2Subgroup(H, true : CosetReps := CosetReps, FindCoset := FindCoset);
end intrinsic;

intrinsic PSL2Subgroup(H::GrpMat,label::MonStgElt) -> GrpGL2Hat
 {returns a subgroup of PSL2(Z) whose image is H (assumes -I in H)}
   ret :=  PSL2Subgroup(H, true);
   ret`Label := label;
   return ret;
end intrinsic;
