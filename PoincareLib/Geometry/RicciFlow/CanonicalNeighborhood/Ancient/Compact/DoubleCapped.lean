import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Cap

/-!
# Strong double-capped tubes on the actual ancient flow

The static caps already carry quantitative estimates. Levi-Civita uniqueness
aligns those estimates and their neck connections with the ancient flow,
preserving the cap/tube attachments. Strong necks on the tube then give the
whole-slice certificate used in Morgan--Tian, Theorem 9.89, pp. 240--241.
-/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Retain both attachments while aligning the cap estimates with the flow connection. -/
def compactStrongDoubleCappedTube
    (K : AncientKappaSolution 3 M) {t epsilon C : ℝ} (ht : t ≤ 0)
    (T : DoubleCappedTubeCertificate (K.flow.metric t))
    (hepsilon₁ : T.cap₁.epsilon = epsilon) (hepsilon₂ : T.cap₂.epsilon = epsilon)
    (htube : T.tube.epsilon = epsilon)
    (hconstant₁ : T.cap₁.cap_constant ≤ C) (hconstant₂ : T.cap₂.cap_constant ≤ C)
    (hstrong : ∀ x ∈ T.tube.carrier,
      ∃ N : StrongEvolvingNeck K t epsilon, N.center = x)
    (hwhole : T.carrier = Set.univ) :
    M26StrongDoubleCappedTube K t epsilon C := {
  time_mem := ht
  epsilon_pos := hepsilon₁ ▸ T.cap₁.epsilon_pos
  constant_pos := T.cap₁.cap_constant_pos.trans_le hconstant₁
  carrier := T.carrier
  cap₁ := NoncompactKappa.strongCapOfCap K ht T.cap₁ hepsilon₁ hconstant₁
  cap₂ := NoncompactKappa.strongCapOfCap K ht T.cap₂ hepsilon₂ hconstant₂
  tube := T.tube
  cap₁_subset := T.cap₁_subset
  cap₂_subset := T.cap₂_subset
  tube_subset := T.tube_subset
  carrier_eq_union := T.carrier_eq_union
  disjoint_cores := T.disjoint_cores
  connected := T.connected
  compact := T.compact
  first_attachment := {
    overlap_model := T.first_attachment.overlap_model
    tube_tail := T.first_attachment.tube_tail
    cap_tail := T.first_attachment.cap_tail
  }
  second_attachment := {
    overlap_model := T.second_attachment.overlap_model
    tube_tail := T.second_attachment.tube_tail
    cap_tail := T.second_attachment.cap_tail
  }
  tube_epsilon := htube
  strong_at := hstrong
  first_cap_connection := rfl
  second_cap_connection := rfl
  carrier_eq_univ := hwhole
}

end PoincareMT
