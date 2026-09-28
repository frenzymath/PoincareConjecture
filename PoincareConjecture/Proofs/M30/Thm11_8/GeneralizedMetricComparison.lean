import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCoefficientLimit
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.M28.Mathlib.RelativeBilinearComparison
import PoincareConjecture.Proofs.M28.Mathlib.FiniteChartCover
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.RelativeMetricReadout












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

set_option maxHeartbeats 800000 in

private theorem eventually_generalized_chart_relative_inner
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    (N : ℕ) (hNt : ∀ k : ℕ, t ∈ Icc (-G.exhaustion.time (k + N)) 0)
    (q : G.limit.carrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 3) q).target)
    {tau : ℝ} (htau : 0 < tau) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3),
      (1 + tau)⁻¹ * (G.limit.flow.metric t).pullbackCoefficients
          (extChartAt (𝓡 3) q).symm x v v ≤
        (normalizedBlowupSliceMetric S (G.subsequence (k + N)) t).pullbackCoefficients
          (generalizedSliceHomeomorph G (k + N) t (hNt k) ∘
            (extChartAt (𝓡 3) q).symm) x v v ∧
      (normalizedBlowupSliceMetric S (G.subsequence (k + N)) t).pullbackCoefficients
          (generalizedSliceHomeomorph G (k + N) t (hNt k) ∘
            (extChartAt (𝓡 3) q).symm) x v v ≤
        (1 + tau) * (G.limit.flow.metric t).pullbackCoefficients
          (extChartAt (𝓡 3) q).symm x v v := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 3) q
  let g := G.limit.flow.metric t
  let A (k : ℕ) :=
    (normalizedBlowupSliceMetric S (G.subsequence (k + N)) t).pullbackCoefficients
      (generalizedSliceHomeomorph G (k + N) t (hNt k) ∘ c.symm)
  change ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : E,
    (1 + tau)⁻¹ * g.pullbackCoefficients c.symm x v v ≤ A k x v v ∧
      A k x v v ≤ (1 + tau) * g.pullbackCoefficients c.symm x v v
  have hc (x : E) (hx : x ∈ K) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (hKt hx))
  have hcont : ContinuousOn (g.pullbackCoefficients c.symm) K :=
    fun x hx => (g.contDiffAt_pullbackCoefficients (hc x hx)).continuousAt.continuousWithinAt
  have hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 →
      0 < g.pullbackCoefficients c.symm x v v := by
    intro x hx v hv
    have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm x).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (hKt hx)
    apply g.pos
    intro hz
    apply hv
    apply hi.injective
    rw [map_zero]
    exact hz
  obtain ⟨alpha, halpha, hlower⟩ :=
    exists_uniform_bilinear_family_lower_bound hK hcont hpos
  have htol : 0 < (tau / (1 + tau)) * alpha := by positivity
  have hconv := tendstoUniformlyOn_generalized_slice_coefficients G ht N hNt q hK hKt
  filter_upwards [(Metric.tendstoUniformlyOn_iff
    (α := E →L[ℝ] E →L[ℝ] ℝ)).mp hconv ((tau / (1 + tau)) * alpha) htol]
    with k hk x hx v
  exact ContinuousLinearMap.relative_quadratic_bounds_of_norm_sub_le
    (g.pullbackCoefficients c.symm x) (A k x) halpha htau (hlower x hx)
    (by simpa only [dist_eq_norm, norm_sub_rev] using (hk x hx).le) v




theorem eventually_generalized_relative_inner
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    (N : ℕ) (hNt : ∀ k : ℕ, t ∈ Icc (-G.exhaustion.time (k + N)) 0)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) {tau : ℝ} (htau : 0 < tau) :
    ∀ᶠ k in atTop,
      K ⊆ (generalizedSliceHomeomorph G (k + N) t (hNt k)).source ∧
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        let e := generalizedSliceHomeomorph G (k + N) t (hNt k)
        let h := normalizedBlowupSliceMetric S (G.subsequence (k + N)) t
        (1 + tau)⁻¹ * (G.limit.flow.metric t).inner x v v ≤
            h.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x v) ∧
          h.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
            (1 + tau) * (G.limit.flow.metric t).inner x v v := by
  classical
  let : LocallyCompactSpace G.limit.carrier.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier
  obtain ⟨s, D, hD, hcover⟩ :=
    hK.exists_finite_extChart_cover (𝓡 3) isOpen_univ (subset_univ _)
  have hall := (Filter.eventually_all_finite s.finite_toSet).mpr fun q hq =>
    eventually_generalized_chart_relative_inner G ht N hNt q
      (hD q hq).2.2.2.2.1 (hD q hq).2.2.2.2.2 htau
  obtain ⟨j, hj⟩ := exists_generalized_exhaustion_stage G hK
  filter_upwards [hall, eventually_ge_atTop j] with k hk hjk
  have hstage : K ⊆ G.exhaustion.space (k + N) :=
    fun x hx => G.exhaustion.space_increasing (by omega) (hj hx)
  refine ⟨hstage, ?_⟩
  intro x hx v
  obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hcover hx)
  have hxD : x ∈ D q := interior_subset hxq
  have hxsource := ((hD q hq).2.2.2.1 hxD).1
  apply RiemannianMetric.relative_inner_bounds_of_chart
    (G.limit.flow.metric t) (normalizedBlowupSliceMetric S (G.subsequence (k + N)) t)
    hxsource
    ((generalizedSliceHomeomorph_contMDiffAt G (k + N) t (hNt k) (hstage hx)).mdifferentiableAt
      (by simp)) _ v
  exact hk q hq _ (mem_image_of_mem _ hxD)




theorem eventually_generalized_tangent_comparison
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    (N : ℕ) (hNt : ∀ k : ℕ, t ∈ Icc (-G.exhaustion.time (k + N)) 0)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) {C : ℝ} (hC : 1 < C) :
    ∀ᶠ k in atTop,
      K ⊆ (generalizedSliceHomeomorph G (k + N) t (hNt k)).source ∧
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        let e := generalizedSliceHomeomorph G (k + N) t (hNt k)
        let h := normalizedBlowupSliceMetric S (G.subsequence (k + N)) t
        h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
            C * (G.limit.flow.metric t).tangentNorm x v ∧
          (G.limit.flow.metric t).tangentNorm x v ≤
            C * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) := by
  have hCp : 0 < C := zero_lt_one.trans hC
  have htau : 0 < C ^ 2 - 1 := by nlinarith
  filter_upwards [eventually_generalized_relative_inner G ht N hNt hK htau] with k hk
  refine ⟨hk.1, ?_⟩
  intro x hx v
  have h := hk.2 x hx v
  dsimp only at h ⊢
  rw [show 1 + (C ^ 2 - 1) = C ^ 2 by ring] at h
  have hlo := mul_le_mul_of_nonneg_left h.1 (sq_nonneg C)
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hCp.ne'), one_mul] at hlo
  constructor
  · simpa only [RiemannianMetric.tangentNorm, Real.sqrt_mul (sq_nonneg C),
      Real.sqrt_sq hCp.le] using Real.sqrt_le_sqrt h.2
  · simpa only [RiemannianMetric.tangentNorm, Real.sqrt_mul (sq_nonneg C),
      Real.sqrt_sq hCp.le] using Real.sqrt_le_sqrt hlo

end PoincareConjecture.M30
