import PoincareConjecture.Proofs.M30.Mathlib.SameSequenceClosedCompactness
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.RetainedCoefficientLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in



theorem exists_closed_coefficient_limit_on_retained_chart
    {n : ℕ} {T τ : ℝ} (hτ : 0 < τ) (hτT : τ < T)
    {S : PointedFlowSequence n (-T / 2) (T / 2)}
    (G : PointedGeometricConvergence S)
    (F : ∀ k, RicciFlow n (S.carrier k).carrier (Icc (-T) 0))
    (hmetric : ∀ k t, (F k).metric t = (S.flow k).flow.metric (t + T / 2))
    (q : G.limitCarrier.carrier) (x₀ : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ (extChartAt (𝓡 n) q).target)
    (α : ℝ) :
    let Ω := Icc (-τ) 0 ×ˢ Metric.closedBall x₀ r
    let f := fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
      ((F (G.subsequence k)).metric z.1).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
          (extChartAt (𝓡 n) q).symm) z.2
    let g := fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (G.limitFlow.flow.metric (z.1 + T / 2)).pullbackCoefficients
        (extChartAt (𝓡 n) q).symm z.2
    (∀ᶠ k : ℕ in atTop, ∀ z ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n),
      α * ‖v‖ ^ 2 ≤ f k z v v) →
    (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop, ∀ z ∈ Ω,
      ‖iteratedFDerivWithin ℝ m (f k) Ω z‖ ≤ C) →
    ∃ B : (ℝ × EuclideanSpace ℝ (Fin n)) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      ContDiffOn ℝ ∞ B Ω ∧ EqOn B g (interior Ω) ∧
      (∀ z ∈ Ω, ∀ v w : EuclideanSpace ℝ (Fin n), B z v w = B z w v) ∧
      (∀ z ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n),
        α * ‖v‖ ^ 2 ≤ B z v v) ∧
      ∀ m : ℕ, TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f k) Ω)
        (iteratedFDerivWithin ℝ m B Ω) atTop Ω := by
  classical
  intro Ω f g hellip hbounds
  have hzero : -T / 2 < 0 ∧ 0 < T / 2 := by constructor <;> linarith
  let c := extChartAt (𝓡 n) q
  have hcompact : IsCompact Ω := isCompact_Icc.prod (isCompact_closedBall x₀ r)
  have hconvex : Convex ℝ Ω := (convex_Icc (-τ) 0).prod (convex_closedBall x₀ r)
  have hinterior : interior Ω = Ioo (-τ) 0 ×ˢ Metric.ball x₀ r := by
    simp only [Ω, interior_prod_eq, interior_Icc, interior_closedBall x₀ hr.ne']
  have hne : (interior Ω).Nonempty := by
    rw [hinterior]
    refine ⟨(-τ / 2, x₀), ⟨by linarith, by linarith⟩, Metric.mem_ball_self hr⟩
  have hc : ContinuousOn c.symm (Metric.closedBall x₀ r) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hball
  obtain ⟨N, hN⟩ := G.exists_exhaustion_superset
    ((isCompact_closedBall x₀ r).image_of_continuousOn hc)
  have hsource : ∀ᶠ k : ℕ in atTop, ContDiffOn ℝ ∞ (f k) Ω := by
    filter_upwards [eventually_ge_atTop N] with k hk
    intro z hz
    have hstage := G.exhaustion_monotone hk (hN (mem_image_of_mem _ hz.2))
    have hψ := (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hstage
    have hchart := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q
      (hball hz.2)).contMDiffAt (extChartAt_target_mem_nhds' (hball hz.2))
    have ht : z.1 ∈ Icc (-T) 0 := ⟨by linarith [hz.1.1], hz.1.2⟩
    exact ((F (G.subsequence k)).smooth.contDiffWithinAt_spacetime_pullbackCoefficients
      (hψ.comp z.2 hchart) ht).mono (fun y hy =>
        ⟨⟨by linarith [hy.1.1], hy.1.2⟩, mem_univ _⟩)
  have hpoint : ∀ z ∈ interior Ω, Tendsto (fun k => f k z) atTop (𝓝 (g z)) := by
    intro z hz
    rw [hinterior] at hz
    have ht : z.1 + T / 2 ∈ Ioo (-T / 2) (T / 2) :=
      ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    have hx := hball (Metric.ball_subset_closedBall hz.2)
    simpa only [f, g, hmetric] using
      tendsto_referenceMap_pullbackCoefficients G hzero q ht hx
  obtain ⟨B, hB, hBg, hjets⟩ :=
    exists_smooth_limit_on_closed_convex_of_eventually_of_pointwise
      hcompact.isClosed hconvex hne f g hsource (by
        intro K _ hKΩ m
        obtain ⟨C, hC, hevent⟩ := hbounds m
        exact ⟨C, hC, hevent.mono fun k hk x hx => hk x (hKΩ hx)⟩) hpoint
  have hconv (m : ℕ) := hjets m Ω hcompact (Subset.refl Ω)
  have hvalues (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ Ω) :
      Tendsto (fun k => f k z) atTop (𝓝 (B z)) := by
    simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using
      (continuous_eval_const (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin n))).continuousAt.tendsto.comp
        ((hconv 0).tendsto_at hz)
  have heval (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ Ω)
      (v w : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun k => f k z v w) atTop (𝓝 (B z v w)) :=
    (continuous_eval_const w).continuousAt.tendsto.comp
      ((continuous_eval_const v).continuousAt.tendsto.comp (hvalues z hz))
  refine ⟨B, hB, hBg, ?_, ?_, hconv⟩
  · intro z hz v w
    apply tendsto_nhds_unique (heval z hz v w)
    apply (heval z hz w v).congr'
    exact Eventually.of_forall fun k => ((F (G.subsequence k)).metric z.1).symm _ _ _
  · intro z hz v
    exact ge_of_tendsto (heval z hz v v) (hellip.mono fun k hk => hk z hz v)

end PoincareConjecture.M30
