freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//                      Access Functions                          //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic Parent(x::SpcHypAElt) -> SpcHypA
   {}
   return x`parent;
end intrinsic;

intrinsic  ScalarField(H::SpcHypA) -> Fld
    {returns the field over which the matrices of H are defined}
    if assigned H`scalar_field then
	return H`scalar_field;
    else
	return Rationals();
    end if;
end intrinsic;


intrinsic ExactValue(x::SpcHypAElt) -> .
    {For x an element of the upperhalf plane, if x is a cusp,
    returns the value of x as an object of type SetCspElt;
    if x has an exact value in a quadratic extension, returns
    this value, as an object of type FldQuadElt; otherwise
    returns a complex value of type FldComElt}
    return x`exact_value;
end intrinsic;

intrinsic Order(x::SpcHypAElt, G::GrpGL2Hat) -> RngIntElt
{For x an element of the upper half plane, returns the order of its stabilier in G.
 If x is an elliptic point returns its order (2 or 3). Otherwise returns infinity. }
  mat := Matrix(Stabilizer(x, G));
  if HasFiniteOrder(mat) then
      if (-G!1 in G) then
	  return Order(mat) div 2;
      else
	  return Order(mat);
      end if;
  else
      return Infinity();
  end if;
end intrinsic;
