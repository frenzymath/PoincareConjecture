import PoincareConjecture.Proofs.M14.Sec6_2_SquareEnergy
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeCurve
import PoincareConjecture.Proofs.M14.Sec6_2_SpatialMetricCoefficients
import PoincareConjecture.Proofs.M14.Mathlib.CompactQuadraticEnergy










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)

private noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dualNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance bilinearNormedGroup :
    NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance bilinearNormedSpace :
    NormedSpace ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace




theorem squarePath_gauge_derivative_memLp (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {U : Set G.Point} (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {a c : ℝ} (hac : a < c) (hAa : Real.sqrt τ₁ ≤ a) (hcB : c ≤ Real.sqrt τ₂)
    (hsrc : ∀ s ∈ Icc a c, p.curve (s ^ 2) ∈ U) :
    let v := fun s => (lift (p.curve (s ^ 2))).2.val
    ContinuousOn v (Icc a c) ∧ (∀ s ∈ Ioo a c, HasDerivAt v (deriv v s) s) ∧
      MemLp (deriv v) 2 (volume.restrict (Icc a c)) := by
  let C := Icc a c
  let θ := fun s => (lift (p.curve (s ^ 2))).1
  let u := fun s => (lift (p.curve (s ^ 2))).2
  let v := fun s => (u s).val
  let x₀ := u a
  let B := fun s => Proofs.M11.ordinaryChartMetric (G.gaugeCover.metric b).metric x₀
    ((θ s).val, (u s).val)
  have hsub : C ⊆ M14SqrtParameterInterval τ₁ τ₂ := Icc_subset_Icc hAa hcB
  have hsubo : Ioo a c ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) := Ioo_subset_Ioo hAa hcB
  have hL := hlift.continuousOn.comp ((squarePath_continuousOn p).mono hsub) hsrc
  have hθ : ContinuousOn (fun s => (θ s).val) C :=
    continuous_subtype_val.comp_continuousOn hL.fst
  have hv : ContinuousOn v C := continuous_subtype_val.comp_continuousOn hL.snd
  have hLreg := (hlift.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp
    ((squarePath_contMDiffOn p).mono hsubo) (fun s hs => hsrc s (Ioo_subset_Icc_self hs))
  have hu : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 u (Ioo a c) :=
    fun s hs => (hLreg s hs).snd
  have hval : ContMDiff (𝓡 n) (𝓡 n) 1
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) := contMDiff_subtype_val
  have hvreg : ContDiffOn ℝ 1 v (Ioo a c) := (hval.comp_contMDiffOn hu).contDiffOn
  have hB : ContinuousOn B C := by
    apply (Proofs.M11.ordinaryChartMetric_smooth (G.gaugeCover.metric b).metric
      (G.gaugeCover.interval b).domain (G.gaugeCover.metric b).smooth x₀).continuousOn.comp
        (hθ.prodMk hv)
    intro s _
    refine ⟨(θ s).property, ?_⟩
    change (u s).val ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).target
    rw [(G.gaugeCover.spatial b).chartAt_target_eq]
    exact (u s).property
  have hpos : ∀ s ∈ C, ∀ w : EuclideanSpace ℝ (Fin n), w ≠ 0 → 0 < B s w w := by
    intro s _ w hw
    dsimp only [B]
    rw [ordinaryChartMetric_openSubset_apply]
    exact ((G.gaugeCover.metric b).metric (θ s).val).pos (u s) w hw
  have henergy : IntervalIntegrable (fun s => G.spacetime.horizontalMetric.inner (p.curve (s ^ 2))
      ((2 * s) • p.horizontal_velocity (s ^ 2)) ((2 * s) • p.horizontal_velocity (s ^ 2)))
      volume a c := by
    apply (squarePath_kinetic_intervalIntegrable p hM12).mono_set
    simpa only [uIcc_of_le hac.le, uIcc_of_le (Real.sqrt_le_sqrt p.tau_lt.le),
      C, M14SqrtParameterInterval] using hsub
  have hcoordinate : IntervalIntegrable (fun s => B s (deriv v s) (deriv v s)) volume a c := by
    apply henergy.congr_uIoo
    intro s hs
    rw [uIoo_of_le hac.le] at hs
    have hsqrt : Real.sqrt s ≠ 0 :=
      (Real.sqrt_pos.mpr ((Real.sqrt_nonneg τ₁).trans_lt (hsubo hs).1)).ne'
    have hbase : (fun r => p.curve (r ^ 2)) =ᶠ[𝓝 s]
        (fun r => (G.gaugeCover.cylinder b).toSpacetime (θ r, u r)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact (hright _ (hsrc r (Ioo_subset_Icc_self hr))).symm
    have htime := ((hLreg s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).fst.mdifferentiableAt
      (by simp)
    have hspace := ((hu s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt (by simp)
    have hpoint : (G.gaugeCover.cylinder b).toSpacetime (θ s, u s) = p.curve (s ^ 2) :=
      hright _ (hsrc s (Ioo_subset_Icc_self hs))
    have hdensity := rawLIntegrand_projectedVelocity_congr (G := G) hbase
    rw [gaugeCurve_rawLIntegrand b θ u htime hspace, M14RawLIntegrand,
      squarePath_projectedVelocity p (hsubo hs), hpoint] at hdensity
    dsimp only [B, v]
    rw [ordinaryChartMetric_openSubset_apply]
    exact add_left_cancel (mul_left_cancel₀ hsqrt hdensity)
  refine ⟨hv, ?_, memLp_two_of_integrable_positive_quadratic hac.le B hB hpos
    (deriv v) (aestronglyMeasurable_deriv _ _) hcoordinate⟩
  intro s hs
  exact ((hvreg s hs).contDiffAt (isOpen_Ioo.mem_nhds hs)).differentiableAt
    (by simp) |>.hasDerivAt

end PoincareConjecture.M14
