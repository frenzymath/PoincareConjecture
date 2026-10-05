import PoincareLib.Geometry.RicciFlow.AncientKappa.Basic

/-!
# Universal noncollapsing output data

The declaration body is unchanged from
`PoincareMT/Definitions/M22UniversalNoncollapsing.lean` at Mapher revision
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

The positive constant is output of the universal noncollapsing theorem.
Reference: Morgan--Tian, Proposition 9.58, pp. 220--221.
-/

set_option autoImplicit false

namespace PoincareMT

structure UniversalNoncollapsingData where
  universal_kappa : ℝ
  universal_kappa_pos : 0 < universal_kappa

end PoincareMT
