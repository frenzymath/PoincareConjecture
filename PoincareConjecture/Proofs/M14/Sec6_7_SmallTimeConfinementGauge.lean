import PoincareConjecture.Proofs.M14.Sec6_2_SquareGaugeEnergy
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeEnergy

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
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

theorem compact_gauge_metric_coercive {K : Set G.Point} (hK : IsCompact K)
    (hlift : ContinuousOn lift K) (x₀ : G.gaugeCover.spatial b) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ q ∈ K, ∀ v : EuclideanSpace ℝ (Fin n),
      κ * ‖v‖ ^ 2 ≤ ((G.gaugeCover.metric b).metric (lift q).1.val).inner (lift q).2 v v := by
  let B := fun q : G.Point =>
    Proofs.M11.ordinaryChartMetric (G.gaugeCover.metric b).metric x₀
      ((lift q).1.val, (lift q).2.val)
  have hB : ContinuousOn B K := by
    apply (Proofs.M11.ordinaryChartMetric_smooth (G.gaugeCover.metric b).metric
      (G.gaugeCover.interval b).domain (G.gaugeCover.metric b).smooth x₀).continuousOn.comp
        ((continuous_subtype_val.comp_continuousOn hlift.fst).prodMk
          (continuous_subtype_val.comp_continuousOn hlift.snd))
    intro q _
    refine ⟨(lift q).1.property, ?_⟩
    change (lift q).2.val ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).target
    rw [(G.gaugeCover.spatial b).chartAt_target_eq]
    exact (lift q).2.property
  have hpos : ∀ q ∈ K, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < B q v v := by
    intro q _ v hv
    dsimp only [B]
    rw [ordinaryChartMetric_openSubset_apply]
    exact ((G.gaugeCover.metric b).metric (lift q).1.val).pos (lift q).2 v hv
  obtain ⟨κ, hκ, hbound⟩ := M08.compact_positive_forms_coercive hK B hB hpos
  refine ⟨κ, hκ, fun q hq v => ?_⟩
  simpa only [B, ordinaryChartMetric_openSubset_apply] using hbound q hq v

theorem squarePath_gauge_prefix_kinetic_eq
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
    {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {a c : ℝ} (hAa : Real.sqrt τ₁ ≤ a) (hcB : c ≤ Real.sqrt τ₂)
    (hsrc : ∀ s ∈ Icc a c, p.curve (s ^ 2) ∈ U)
    {s : ℝ} (hs : s ∈ Ioo a c) :
    ((G.gaugeCover.metric b).metric (lift (p.curve (s ^ 2))).1.val).inner
      (lift (p.curve (s ^ 2))).2
      (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s)
      (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s) = pathSquareKinetic p s := by
  let θ := fun r => (lift (p.curve (r ^ 2))).1
  let v := fun r => (lift (p.curve (r ^ 2))).2
  have hsub : Ioo a c ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) := Ioo_subset_Ioo hAa hcB
  have hLreg := (hlift.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp
    ((squarePath_contMDiffOn p).mono hsub) (fun r hr => hsrc r (Ioo_subset_Icc_self hr))
  have htime := ((hLreg s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).fst.mdifferentiableAt
    (by simp)
  have hspace := ((hLreg s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).snd.mdifferentiableAt
    (by simp)
  have hbase : (fun r => p.curve (r ^ 2)) =ᶠ[𝓝 s]
      (fun r => (G.gaugeCover.cylinder b).toSpacetime (θ r, v r)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact (hright _ (hsrc r (Ioo_subset_Icc_self hr))).symm
  have hpoint : (G.gaugeCover.cylinder b).toSpacetime (θ s, v s) = p.curve (s ^ 2) :=
    hright _ (hsrc s (Ioo_subset_Icc_self hs))
  have hdensity := rawLIntegrand_projectedVelocity_congr (G := G) hbase
  rw [gaugeCurve_rawLIntegrand b θ v htime hspace, M14RawLIntegrand,
    squarePath_projectedVelocity p (hsub hs), hpoint] at hdensity
  have hsqrt : Real.sqrt s ≠ 0 :=
    (Real.sqrt_pos.mpr ((Real.sqrt_nonneg τ₁).trans_lt (hsub hs).1)).ne'
  exact (add_left_cancel (mul_left_cancel₀ hsqrt hdensity)).symm

end PoincareConjecture.M14
