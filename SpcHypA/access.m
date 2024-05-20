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

