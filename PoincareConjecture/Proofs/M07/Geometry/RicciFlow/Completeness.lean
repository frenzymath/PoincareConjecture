import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Pointed
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormBounds
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Completeness











set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareConjecture.BasedFlow



theorem complete_interior_of_two_time_curvature_bound
    {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    (F : BasedFlow n T' T C) (hT : T' < 0 ∧ 0 < T)
    (hcomplete : C.metricComplete (F.metricAt 0))
    (hcurv : ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ s ∈ Set.Ioo T' T, ∀ t ∈ Set.Ioo T' T,
        ∀ x ∈ F.ballAt s A, (F.flow.connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Set.Ioo T' T, C.metricComplete (F.metricAt t) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : T2Space C.carrier := C.t2Space
  intro t ht
  let d₀ := (C.metricEMetricSpace (F.metricAt 0)).toPseudoEMetricSpace
  let d₁ := (C.metricEMetricSpace (F.metricAt t)).toPseudoEMetricSpace
  change @CompleteSpace C.carrier d₁.toUniformSpace
  apply Poincare.completeSpace_of_continuous_local_edist_bound d₀ d₁ F.base hcomplete
  · change @Continuous C.carrier C.carrier C.topologicalSpace C.topologicalSpace id
    exact continuous_id
  · exact fun x ↦ @Poincare.edist_ne_top_of_preconnected C.carrier d₁
      (C.preconnected_metricEMetricSpace (F.metricAt t)) x F.base
  · intro R
    let r : ℝ := R + 1
    have hr : 0 < r := by dsimp [r]; positivity
    obtain ⟨K, _, hK⟩ := hcurv (3 * r) (by positivity)
    let L : ℝ := (n : ℝ) ^ 3 * K
    let A : ℝ := Real.exp (L * |0 - t|)
    refine ⟨Real.toNNReal A, fun x y hx hy ↦ ?_⟩
    have hRic : ∀ τ ∈ Set.Ioo T' T, ∀ z ∈ (F.flow.metric t).ball F.base (3 * r),
        ∀ v : C.tangent z,
          |(F.flow.connection τ).ricci z v v| ≤ L * (F.flow.metric τ).inner z v v := by
      intro τ hτ z hz v
      have hQ : 0 ≤ (F.flow.metric τ).inner z v v := by
        by_cases hv : v = 0
        · subst v; simp
        · exact ((F.flow.metric τ).pos z v hv).le
      have hnorm := (F.flow.connection τ).abs_ricci_quadratic_le_curvatureTensorNorm z v
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) z) = n := finrank_euclideanSpace_fin
      simp only [Fintype.card_fin, hdim] at hnorm
      exact hnorm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hK t ht τ hτ z hz) (by positivity)) hQ)
    have hR : (R : ℝ≥0∞) < ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_lt_ofReal_iff hr |>.mpr (by dsimp [r]; linarith)
    have hmem (z : C.carrier) (hz : d₁.edist z F.base ≤ R) :
        z ∈ (F.flow.metric t).ball F.base r := by
      change d₁.edist F.base z < ENNReal.ofReal r
      rw [d₁.edist_comm]
      exact hz.trans_lt hR
    have hdist := F.flow.edist_le_exp_mul_of_ricci_bound (convex_Ioo T' T)
      (Set.Subset.refl _) F.base r L hr ht hT hRic (hmem x hx) (hmem y hy)
    change (F.flow.metric 0).edist x y ≤ ENNReal.ofReal A *
      (F.flow.metric t).edist x y
    exact hdist

end PoincareConjecture.BasedFlow
