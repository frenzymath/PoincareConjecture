import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.PastSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Round
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.TwoCaps.Diameter

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ConnectedSpace M] {g : RiemannianMetric 3 M}

theorem metricDiameter_mul_sqrt_scalar_lt_of_two_cap_cover
    (A B : CapCertificate g) (D : LeviCivitaData g) {C : ℝ} (hC : 0 < C)
    (hA : A.cap_constant ≤ C) (hB : B.cap_constant ≤ C)
    (hcover : A.carrier ∪ B.carrier = univ) (x : M) :
    metricDiameter g univ * Real.sqrt (D.scalarCurvature x) < twoCapDiameterConstant C := by
  have hx : x ∈ A.carrier ∪ B.carrier := by rw [hcover]; exact mem_univ x
  have hscalar : 0 < D.scalarCurvature x := by
    rcases hx with hx | hx
    · rw [← A.connection.scalarCurvature_eq D x]
      exact A.scalar_pos x hx
    · rw [← B.connection.scalarCurvature_eq D x]
      exact B.scalar_pos x hx
  have hsqrt := Real.sqrt_pos.mpr hscalar
  have hcancel : D.scalarCurvature x ^ (-1 / 2 : ℝ) *
      Real.sqrt (D.scalarCurvature x) = 1 := by
    rw [neg_div, Real.rpow_neg hscalar.le, ← Real.sqrt_eq_rpow,
      inv_mul_cancel₀ hsqrt.ne']
  have hbound := mul_lt_mul_of_pos_right
    (A.metricDiameter_lt_of_two_cap_cover B D hC hA hB hcover x) hsqrt
  simpa only [mul_assoc, hcancel, mul_one] using hbound

end CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem compact_nonround_exists_earlier_slice_not_round_or_two_caps
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : AncientKappaSolution 3 M) (hcompact : IsCompact (univ : Set M))
    (hnonround : ¬ IsRoundAncientKappaSolution K) (C : ℝ) (hC : 0 < C) (b : ℝ) :
    ∃ t : ℝ, t < min b 0 ∧ ∃ p : M,
      max 10 (twoCapDiameterConstant C) <
        metricDiameter (K.flow.metric t) univ *
          Real.sqrt ((K.flow.connection t).scalarCurvature p) ∧
      ¬ ConstantPositiveSectionalCurvature (K.flow.metric t) (K.flow.connection t) ∧
      ¬ ∃ A B : CapCertificate (K.flow.metric t),
        A.cap_constant ≤ C ∧ B.cap_constant ≤ C ∧ A.carrier ∪ B.carrier = univ := by
  obtain ⟨t, ht, p, hdiam⟩ := compact_nonround_exists_earlier_large_scalarDiameter
    P K hcompact hnonround (max 10 (twoCapDiameterConstant C)) b
  refine ⟨t, ht, p, hdiam, ?_, ?_⟩
  · intro hround
    have hbound := round_metricDiameter_mul_sqrt_scalar_le (K.flow.metric t)
      (K.flow.connection t) (K.complete t (ht.le.trans (min_le_right _ _))) hround p
    exact (not_le_of_gt ((le_max_left _ _).trans_lt hdiam)) hbound
  · rintro ⟨A, B, hA, hB, hcover⟩
    have hbound := A.metricDiameter_mul_sqrt_scalar_lt_of_two_cap_cover B
      (K.flow.connection t) hC hA hB hcover p
    exact (not_lt_of_ge ((le_max_right _ _).trans hdiam.le)) hbound

end PoincareConjecture
