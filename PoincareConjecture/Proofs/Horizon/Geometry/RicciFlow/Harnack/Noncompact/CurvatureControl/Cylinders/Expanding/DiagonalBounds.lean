import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.Bounds
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Eventual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem diagonal_referenceCharts_analytic_bounds_of_estimates
    {n : ℕ} {T' T δ : ℝ} (S : PointedFlowSequence n T' T)
    {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (hparams : ∀ j, 0 < ρ j ∧ 2 * ρ j < R j ∧ 0 < a j ∧ 0 < b j)
    (cover : ∀ k j, j ≤ k → NormalChartCover (S.flow k).flow.metric
      (S.flow k).base T' T ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j))
    (hestimates : ∀ j (I : Set ℝ), IsCompact I → I ⊆ Iio δ →
      ∃ s c : ℝ, I ⊆ Ioo s δ ∧ 0 < c ∧
        (∀ᶠ k in atTop, ∀ hjk : j ≤ k, ∀ i,
          ContDiffOn ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((S.flow k).flow.metric z.1).pullbackCoefficients
              ((cover k j hjk).chart i) z.2) (Ioo s δ ×ˢ Metric.ball 0 (R j)) ∧
          ∀ t ∈ Ioo s δ, ∀ x ∈ Metric.closedBall 0 (2 * ρ j), ∀ v,
            c * ‖v‖ ^ 2 ≤ ((S.flow k).flow.metric t).pullbackCoefficients
              ((cover k j hjk).chart i) x v v) ∧
        ∀ d : ℕ, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ hjk : j ≤ k, ∀ i,
          ∀ t ∈ I, ∀ x ∈ Metric.closedBall 0 (ρ j),
            ‖iteratedFDeriv ℝ d (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              ((S.flow k).flow.metric z.1).pullbackCoefficients
                ((cover k j hjk).chart i) z.2) (t, x)‖ ≤ B) :
    ∀ i : ℕ,
      let raw := fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
            ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
              Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2
      LocallyEventuallyContDiff (Iio δ ×ˢ Metric.ball 0 (ρ (Nat.unpair i).1)) raw ∧
      (∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
        K ⊆ Iio δ ×ˢ Metric.ball 0 (ρ (Nat.unpair i).1) → ∀ d : ℕ, ∃ B : ℝ,
          ∀ᶠ k in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ d (raw k) z‖ ≤ B) ∧
      (∀ t ∈ Iio δ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
        ∀ x ∈ Metric.ball 0 (ρ (Nat.unpair i).1), ∀ v,
          c * ‖v‖ ^ 2 ≤ raw k (t, x) v v) := by
  intro i
  let j := (Nat.unpair i).1
  let l : Fin (N j + 1) :=
    ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  let rawStage := fun k j (hk : j ≤ k) (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
    ((S.flow k).flow.metric z.1).pullbackCoefficients
      ((cover k j hk).chart
        ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2
  let raw := fun k => rawStage k (min j k) (min_le_right _ _)
  change LocallyEventuallyContDiff (Iio δ ×ˢ Metric.ball 0 (ρ j)) raw ∧ _
  have hstage (k : ℕ) (hk : j ≤ k) : raw k =
      fun z => ((S.flow k).flow.metric z.1).pullbackCoefficients
        ((cover k j hk).chart l) z.2 := by
    funext z
    change rawStage k (min j k) (min_le_right _ _) z = rawStage k j hk z
    simp only [min_eq_left hk]
  refine ⟨?_, ?_, ?_⟩
  · intro K hK hKΩ
    have hKI : Prod.fst '' K ⊆ Iio δ := by
      rintro t ⟨z, hz, rfl⟩
      exact (hKΩ hz).1
    obtain ⟨s, c, htime, hc, hsmooth, _⟩ :=
      hestimates j _ (hK.image continuous_fst) hKI
    filter_upwards [hsmooth, eventually_ge_atTop j] with k hk hkj
    refine ⟨Ioo s δ ×ˢ Metric.ball 0 (R j), isOpen_Ioo.prod Metric.isOpen_ball, ?_, ?_⟩
    · intro z hz
      exact ⟨htime (mem_image_of_mem Prod.fst hz),
        Metric.ball_subset_ball (by linarith [(hparams j).1, (hparams j).2.1])
          (hKΩ hz).2⟩
    · rw [hstage k hkj]
      exact (hk hkj l).1
  · intro K hK hKΩ d
    have hKI : Prod.fst '' K ⊆ Iio δ := by
      rintro t ⟨z, hz, rfl⟩
      exact (hKΩ hz).1
    obtain ⟨s, c, htime, hc, hsmooth, hjets⟩ :=
      hestimates j _ (hK.image continuous_fst) hKI
    obtain ⟨B, hbound⟩ := hjets d
    refine ⟨B, ?_⟩
    filter_upwards [hbound, eventually_ge_atTop j] with k hk hkj
    intro z hz
    change ‖iteratedFDeriv ℝ d (raw k) z‖ ≤ B
    rw [hstage k hkj]
    exact hk hkj l z.1 (mem_image_of_mem Prod.fst hz) z.2
      (Metric.ball_subset_closedBall (hKΩ hz).2)
  · intro t ht
    obtain ⟨s, c, htime, hc, hbound, _⟩ :=
      hestimates j _ isCompact_singleton (singleton_subset_iff.mpr ht)
    refine ⟨c, hc, ?_⟩
    filter_upwards [hbound, eventually_ge_atTop j] with k hk hkj
    intro x hx v
    change c * ‖v‖ ^ 2 ≤ raw k (t, x) v v
    rw [hstage k hkj]
    exact (hk hkj l).2 t (htime (mem_singleton t)) x
      (Metric.closedBall_subset_closedBall (by linarith [(hparams j).1])
        (Metric.ball_subset_closedBall hx)) v

end PoincareConjecture.RicciFlow
