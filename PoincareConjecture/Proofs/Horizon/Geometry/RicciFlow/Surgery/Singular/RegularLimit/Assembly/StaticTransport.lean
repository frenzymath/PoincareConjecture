import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.SliceIdentifications
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.CanonicalNeighborhood









set_option autoImplicit false

universe u

namespace PoincareConjecture.SingularRegularLimit.SliceGeometry

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

end PoincareConjecture.SingularRegularLimit.SliceGeometry
