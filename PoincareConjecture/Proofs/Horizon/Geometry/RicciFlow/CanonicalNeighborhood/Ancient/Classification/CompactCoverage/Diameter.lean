import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.VolumeDiameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.RelativeScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Normalization











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



theorem compact_uniform_scalar_ratio_of_scaled_diameter_of_m27
    (P : M27KappaAlternativePredecessors.{u})
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K → IsCompact (univ : Set M) →
        Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          metricDiameter (K.flow.metric 0) univ ≤ D →
        ∀ x : M, (K.flow.connection 0).scalarCurvature x ≤
          C * (K.flow.connection 0).scalarCurvature p := by
  obtain ⟨kappa, hkappa, hnoncollapsed⟩ := P.universal_noncollapsing
  obtain ⟨C, hC, hbound⟩ := normalized_compact_uniform_scalar_upper P hkappa hD
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnonround hcompact hdiam x
  let L : AncientKappaSolution 3 M := {
    K with
    kappa := kappa
    kappa_pos := hkappa
    noncollapsed := hnoncollapsed K hnonround }
  obtain ⟨N⟩ := P.normalization M L p 0 le_rfl
  have hscale : N.scale = (K.flow.connection 0).scalarCurvature p := N.scale_eq
  have htarget : AncientKappaNoncollapsed N.target.flow kappa := by
    have hk : N.target.kappa = kappa := N.target_kappa
    rw [← hk]
    exact N.target.noncollapsed
  have hnormalizedDiameter : metricDiameter (N.target.flow.metric 0) univ ≤ D := by
    rw [N.metricDiameter_zero, hscale]
    exact hdiam
  have hscalar := hbound N.target p htarget N.normalized_scalar hcompact
    hnormalizedDiameter x
  rw [N.scalar_eq 0 le_rfl x, zero_div, zero_add] at hscalar
  have hresult := (div_le_iff₀ N.scale_pos).mp hscalar
  simpa only [L, hscale] using hresult



theorem compact_uniform_allPoint_diameter_bound_of_m27
    (P : M27KappaAlternativePredecessors.{u})
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K → IsCompact (univ : Set M) →
        Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          metricDiameter (K.flow.metric 0) univ ≤ D →
        ∀ x : M, metricDiameter (K.flow.metric 0) univ <
          C * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := compact_uniform_scalar_ratio_of_scaled_diameter_of_m27 P hD
  refine ⟨D * Real.sqrt C + 1, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnonround hcompact hdiam x
  obtain ⟨N⟩ := P.normalization M K x 0 le_rfl
  have hxpos : 0 < (K.flow.connection 0).scalarCurvature x := N.scale_eq ▸ N.scale_pos
  have hcomparison := Real.sqrt_le_sqrt (hbound K p hnonround hcompact hdiam x)
  rw [Real.sqrt_mul hC.le] at hcomparison
  have hdiam_nonneg : 0 ≤ metricDiameter (K.flow.metric 0) univ :=
    ENNReal.toReal_nonneg.trans
      (compact_toReal_edist_le_metricDiameter (K.flow.metric 0) hcompact p p)
  have hscaled : Real.sqrt ((K.flow.connection 0).scalarCurvature x) *
      metricDiameter (K.flow.metric 0) univ ≤ Real.sqrt C * D := by
    calc
      _ ≤ (Real.sqrt C * Real.sqrt ((K.flow.connection 0).scalarCurvature p)) *
          metricDiameter (K.flow.metric 0) univ :=
        mul_le_mul_of_nonneg_right hcomparison hdiam_nonneg
      _ = Real.sqrt C * (Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          metricDiameter (K.flow.metric 0) univ) := by ring
      _ ≤ Real.sqrt C * D := mul_le_mul_of_nonneg_left hdiam (Real.sqrt_nonneg C)
  have hpower : (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) =
      (Real.sqrt ((K.flow.connection 0).scalarCurvature x))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hxpos.le,
      ← Real.sqrt_eq_rpow]
  rw [hpower, ← div_eq_mul_inv]
  apply (lt_div_iff₀ (Real.sqrt_pos.mpr hxpos)).mpr
  nlinarith

end PoincareConjecture
