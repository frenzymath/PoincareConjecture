import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.SliceIdentifications
import PoincareLib.Geometry.RicciFlow.Generalized.CanonicalNeighborhood

/-!
# Static canonical certificates on equal linked slice geometries

The terminal geometry is identified with the regular region by equality of
the full slice geometry. Transport therefore preserves each certificate's
metric, connection, carrier and calibration together.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.SingularRegularLimit.SliceGeometry

variable {G K : SliceGeometry.{u}}

theorem exists_cComponent_of_eq (h : G = K) (x : G.slice.carrier) {C : ℝ}
    (hN : ∃ N : SingularCComponent K.metric K.connection C,
      homeomorphOfEq h x ∈ N.carrier) :
    ∃ N : SingularCComponent G.metric G.connection C, x ∈ N.carrier := by
  subst K
  exact hN

theorem exists_roundComponent_of_eq (h : G = K) (x : G.slice.carrier) {ε : ℝ}
    (hN : ∃ N : SingularRoundComponent K.metric ε,
      homeomorphOfEq h x ∈ N.carrier) :
    ∃ N : SingularRoundComponent G.metric ε, x ∈ N.carrier := by
  subst K
  exact hN

theorem exists_cap_of_eq (h : G = K) (x : G.slice.carrier) {ε C : ℝ}
    (hN : ∃ N : CapCertificate K.metric, N.epsilon = ε ∧ N.cap_constant ≤ C ∧
      N.connection = K.connection ∧ homeomorphOfEq h x ∈ N.core) :
    ∃ N : CapCertificate G.metric, N.epsilon = ε ∧ N.cap_constant ≤ C ∧
      N.connection = G.connection ∧ x ∈ N.core := by
  subst K
  exact hN

end PoincareMT.SingularRegularLimit.SliceGeometry
