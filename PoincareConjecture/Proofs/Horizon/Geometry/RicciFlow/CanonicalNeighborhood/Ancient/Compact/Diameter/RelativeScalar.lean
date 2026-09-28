import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Length












set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

section Normalization

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p : M}

set_option backward.isDefEq.respectTransparency false in


theorem AncientKappaNormalization.toReal_edist_zero
    (N : AncientKappaNormalization K p 0) (x y : M) :
    ((N.target.flow.metric 0).edist x y).toReal =
      Real.sqrt N.scale * ((K.flow.metric 0).edist x y).toReal := by
  have hmetric : MetricHomothety (K.flow.metric 0) (N.target.flow.metric 0)
      (Diffeomorph.refl (𝓡 3) M ∞) N.scale := by
    intro z v w
    simpa [Diffeomorph.coe_refl, mfderiv_id] using N.metric_eq 0 z v w
  have hdist := Homothety.homothety_edist (K.flow.metric 0) (N.target.flow.metric 0)
    (Diffeomorph.refl (𝓡 3) M ∞) N.scale N.scale_pos hmetric x y
  change (N.target.flow.metric 0).edist x y = _ at hdist
  rw [hdist, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

end Normalization



theorem compact_uniform_scalar_ratio_of_scaled_diameter
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        IsCompact (Set.univ : Set M) →
        Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          metricDiameter (K.flow.metric 0) Set.univ ≤ D →
        ∀ x : M, (K.flow.connection 0).scalarCurvature x ≤
          C * (K.flow.connection 0).scalarCurvature p := by
  obtain ⟨kappa, hkappa, hnoncollapsed⟩ := P.universal_noncollapsing
  obtain ⟨C, hC, hbound⟩ := compact_uniform_scalar_bound_of_normalized P hkappa
    (show 0 < D + 1 by linarith)
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnonround hcompact hdiam x
  let L : AncientKappaSolution 3 M := {
    K with
    kappa := kappa
    kappa_pos := hkappa
    noncollapsed := hnoncollapsed K hnonround
  }
  obtain ⟨N⟩ := P.normalization M L p 0 le_rfl
  have hscale : N.scale = (K.flow.connection 0).scalarCurvature p := N.scale_eq
  have htarget : AncientKappaNoncollapsed N.target.flow kappa := by
    have hk : N.target.kappa = kappa := N.target_kappa
    rw [← hk]
    exact N.target.noncollapsed
  have hx : x ∈ (N.target.flow.metric 0).ball p (D + 1) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt ((N.target.flow.metric 0).edist_ne_top p x)).mpr
    rw [N.toReal_edist_zero, hscale]
    change Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
      ((K.flow.metric 0).edist p x).toReal < D + 1
    exact ((mul_le_mul_of_nonneg_left
      (compact_toReal_edist_le_metricDiameter (K.flow.metric 0) hcompact p x)
      (Real.sqrt_nonneg _)).trans hdiam).trans_lt (by linarith)
  have hscalar := hbound N.target p htarget N.normalized_scalar x hx
  rw [N.scalar_eq 0 le_rfl x, zero_div, zero_add] at hscalar
  have hresult := (div_le_iff₀ N.scale_pos).mp hscalar
  simpa only [L, hscale] using hresult



theorem compact_uniform_allPoint_diameter_bound
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        IsCompact (Set.univ : Set M) →
        Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          metricDiameter (K.flow.metric 0) Set.univ ≤ D →
        ∀ x : M, metricDiameter (K.flow.metric 0) Set.univ <
          C * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := compact_uniform_scalar_ratio_of_scaled_diameter P hD
  refine ⟨D * Real.sqrt C + 1, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnonround hcompact hdiam x
  obtain ⟨N⟩ := P.normalization M K x 0 le_rfl
  have hxpos : 0 < (K.flow.connection 0).scalarCurvature x :=
    N.scale_eq ▸ N.scale_pos
  have hcomparison := Real.sqrt_le_sqrt (hbound K p hnonround hcompact hdiam x)
  rw [Real.sqrt_mul hC.le] at hcomparison
  have hdiam_nonneg : 0 ≤ metricDiameter (K.flow.metric 0) Set.univ :=
    ENNReal.toReal_nonneg.trans
      (compact_toReal_edist_le_metricDiameter (K.flow.metric 0) hcompact p p)
  have hscaled : Real.sqrt ((K.flow.connection 0).scalarCurvature x) *
      metricDiameter (K.flow.metric 0) Set.univ ≤ Real.sqrt C * D := by
    calc
      _ ≤ (Real.sqrt C * Real.sqrt ((K.flow.connection 0).scalarCurvature p)) *
          metricDiameter (K.flow.metric 0) Set.univ :=
        mul_le_mul_of_nonneg_right hcomparison hdiam_nonneg
      _ = Real.sqrt C * (Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          metricDiameter (K.flow.metric 0) Set.univ) := by ring
      _ ≤ Real.sqrt C * D := mul_le_mul_of_nonneg_left hdiam (Real.sqrt_nonneg C)
  have hpower : (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) =
      (Real.sqrt ((K.flow.connection 0).scalarCurvature x))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hxpos.le,
      ← Real.sqrt_eq_rpow]
  rw [hpower, ← div_eq_mul_inv]
  apply (lt_div_iff₀ (Real.sqrt_pos.mpr hxpos)).mpr
  nlinarith

end PoincareConjecture
