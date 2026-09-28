import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.DiagonalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.ChartBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem diagonal_referenceCharts_analytic_bounds_of_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    {T' T : ℝ} (S : PointedFlowSequence (m + 1) T' T) (hT : T' < 0 ∧ 0 < T)
    (J : ℕ → Set ℝ) (F : ∀ k, RicciFlow (m + 1) (S.carrier k).carrier (J k))
    (A L : ℕ → ℝ) (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (S.carrier k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (S.flow k).base (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤ ((F k).metric 0).volumeMeasure
      (((F k).metric 0).ball (S.flow k).base 1))
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1)
    (hmetric : ∀ k t, (S.flow k).flow.metric t = (F k).metric (t - δ))
    {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (hparams : ∀ j, 0 < ρ j ∧ 2 * ρ j < R j ∧ 0 < a j ∧ 0 < b j)
    (cover : ∀ k j, j ≤ k → NormalChartCover (S.flow k).flow.metric
      (S.flow k).base T' T ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j)) :
    ∀ i : ℕ,
      let raw := fun k (z : ℝ × EuclideanSpace ℝ (Fin (m + 1))) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
            ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
              Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2
      LocallyEventuallyContDiff (Iio δ ×ˢ Metric.ball 0 (ρ (Nat.unpair i).1)) raw ∧
      (∀ K : Set (ℝ × EuclideanSpace ℝ (Fin (m + 1))), IsCompact K →
        K ⊆ Iio δ ×ˢ Metric.ball 0 (ρ (Nat.unpair i).1) → ∀ d : ℕ, ∃ B : ℝ,
          ∀ᶠ k in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ d (raw k) z‖ ≤ B) ∧
      (∀ t ∈ Iio δ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
        ∀ x ∈ Metric.ball 0 (ρ (Nat.unpair i).1), ∀ v,
          c * ‖v‖ ^ 2 ≤ raw k (t, x) v v) := by
  apply diagonal_referenceCharts_analytic_bounds_of_estimates S hparams cover
  intro j I hIcompact hI
  obtain ⟨s, a', b', hs, htime, ha', hb', hsmooth, hjets⟩ :=
    eventually_referenceChart_estimates_of_expanding_cylinders hC hm S.carrier J F
      (fun k => (S.flow k).base) A L hA hL hJ hcomplete hoperator hscalar hν hvolume
      hδ hδone hT (by positivity : 0 < (j : ℝ) + 1) (hparams j).1
      (hparams j).2.1 (hparams j).2.2.1 (hparams j).2.2.2 (N := N j) hIcompact hI
  have hmetricFun (k : ℕ) : (fun t => (F k).metric (t - δ)) =
      (S.flow k).flow.metric := (funext (hmetric k)).symm
  refine ⟨s, a', htime, ha', ?_, ?_⟩
  · filter_upwards [hsmooth] with k hk
    rw [hmetricFun k] at hk
    simp_rw [← hmetric k] at hk
    intro hjk i
    exact ⟨(hk (cover k j hjk) i).1,
      fun t ht x hx v => ((hk (cover k j hjk) i).2 t ht x hx v).1⟩
  · intro d
    obtain ⟨B, _, hbound⟩ := hjets d
    refine ⟨B, ?_⟩
    filter_upwards [hbound] with k hk
    rw [hmetricFun k] at hk
    simp_rw [← hmetric k] at hk
    exact fun hjk => hk (cover k j hjk)

end PoincareConjecture.RicciFlow
