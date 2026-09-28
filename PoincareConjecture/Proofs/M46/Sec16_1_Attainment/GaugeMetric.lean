import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeGaugeAction
import PoincareConjecture.Proofs.M14.Sec6_1_PathRestriction
import PoincareConjecture.Proofs.M08.ChartCoercivity









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  (j : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j) (x0 : G.gaugeCover.spatial j)

private noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dualNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance bilinearNormedGroup :
    NormedAddCommGroup
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance bilinearNormedSpace :
    NormedSpace ℝ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



noncomputable def gaugeLiftMetric (q : G.Point) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  Proofs.M11.ordinaryChartMetric (G.gaugeCover.metric j).metric x0
    ((lift q).1.val, (lift q).2.val)



theorem gaugeLiftMetric_apply (q : G.Point) (v w : EuclideanSpace ℝ (Fin 3)) :
    gaugeLiftMetric j lift x0 q v w =
      ((G.gaugeCover.metric j).metric (lift q).1.val).inner (lift q).2 v w :=
  M14.ordinaryChartMetric_openSubset_apply _ _ _ _ _ _ _




theorem gaugeLiftMetric_continuousOn {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel 3) (spacetimeModel 3) ∞ lift U) :
    ContinuousOn (gaugeLiftMetric j lift x0) U := by
  apply (Proofs.M11.ordinaryChartMetric_smooth (G.gaugeCover.metric j).metric
    (G.gaugeCover.interval j).domain (G.gaugeCover.metric j).smooth x0).continuousOn.comp
      ((continuous_subtype_val.comp_continuousOn hlift.continuousOn.fst).prodMk
        (continuous_subtype_val.comp_continuousOn hlift.continuousOn.snd))
  intro q _
  refine ⟨(lift q).1.property, ?_⟩
  change (lift q).2.val ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) x0).target
  rw [(G.gaugeCover.spatial j).chartAt_target_eq]
  exact (lift q).2.property




theorem compact_gaugeLiftMetric_coercive {U K : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel 3) (spacetimeModel 3) ∞ lift U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ q ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3),
      c * ‖v‖ ^ 2 ≤ gaugeLiftMetric j lift x0 q v v := by
  apply M08.compact_positive_forms_coercive hK (gaugeLiftMetric j lift x0)
    ((gaugeLiftMetric_continuousOn j lift x0 hlift).mono hKU)
  intro q _ v hv
  rw [gaugeLiftMetric_apply]
  exact ((G.gaugeCover.metric j).metric (lift q).1.val).pos (lift q).2 v hv




theorem squarePath_gaugeLiftMetric_eq {T tau : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T 0 tau x y) {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel 3) (spacetimeModel 3) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    {a b s : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.sqrt tau) (hs : s ∈ Ioo a b)
    (hsrc : ∀ r ∈ Icc a b, p.curve (r ^ 2) ∈ U) :
    gaugeLiftMetric j lift x0 (p.curve (s ^ 2))
      (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s)
      (deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s) = M14.pathSquareKinetic p s := by
  have hab := hs.1.trans hs.2
  have hb0 := ha.trans hab.le
  have hab2 : a ^ 2 < b ^ 2 := (sq_lt_sq₀ ha hb0).mpr hab
  have hb2 : b ^ 2 ≤ tau := by
    simpa only [Real.sq_sqrt p.tau_lt.le] using
      (sq_le_sq₀ hb0 (Real.sqrt_nonneg tau)).mpr hb
  let q := M14.restrictPath p (a ^ 2) (b ^ 2) (sq_nonneg a) hab2 hb2
  have hsrcq : ∀ r ∈ M14SqrtParameterInterval (a ^ 2) (b ^ 2), q.curve (r ^ 2) ∈ U := by
    intro r hr
    apply hsrc r
    simpa only [M14SqrtParameterInterval, Real.sqrt_sq ha, Real.sqrt_sq hb0] using hr
  have hsq : s ∈ Ioo (Real.sqrt (a ^ 2)) (Real.sqrt (b ^ 2)) := by
    simpa only [Real.sqrt_sq ha, Real.sqrt_sq hb0] using hs
  have h := M14.squarePath_gauge_kinetic_eq q j lift x0 hlift hright hsrcq hsq
  have hclock := M14.gaugeLift_time_eq q j lift hright
    (M14.squarePath_parameter_mem q (Ioo_subset_Icc_self hsq))
    (hsrcq s (Ioo_subset_Icc_self hsq))
  change (lift (p.curve (s ^ 2))).1.val = T - s ^ 2 at hclock
  unfold gaugeLiftMetric
  rw [hclock]
  exact h

end PoincareConjecture.Proofs.M46
