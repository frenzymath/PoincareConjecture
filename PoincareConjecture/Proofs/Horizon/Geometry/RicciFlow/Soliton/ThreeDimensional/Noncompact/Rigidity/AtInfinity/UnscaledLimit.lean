import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.UnscaledSource
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.GeometricLimit.NormalCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Universe
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Preservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Completeness







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle ENNReal Topology

noncomputable section

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)

private theorem compact_time_window {I : Set ℝ} (hI : IsCompact I) (hI1 : I ⊆ Iio 1) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ b < 1 ∧ I ⊆ Ioo a b := by
  obtain ⟨l, hl⟩ := hI.bddBelow
  by_cases hne : I.Nonempty
  · obtain ⟨u, hu⟩ := hI.exists_isGreatest hne
    refine ⟨min (-1) (l - 1), max (1 / 2) ((u + 1) / 2),
      (min_le_left _ _).trans_lt (by norm_num),
      lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_, ?_⟩
    · apply max_lt (by norm_num)
      have := hI1 hu.1
      change u < 1 at this
      linarith
    · intro t ht
      constructor
      · have := min_le_right (-1 : ℝ) (l - 1)
        linarith [hl ht]
      · have := le_max_right (1 / 2 : ℝ) ((u + 1) / 2)
        have hut : u < 1 := hI1 hu.1
        linarith [hu.2 ht]
  · exact ⟨-1, 1 / 2, by norm_num, by norm_num, by norm_num,
      fun _ ht => (hne ⟨_, ht⟩).elim⟩



theorem exists_unscaledPointedLimit (hC : RicciFlowCurvatureTheory.{u}) (q : ℕ → M) :
    ∃ L : AncientPointedGeometricConvergence
        (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
        (fun _ => G.unscaledSourceFlow.shrink.metric)
        (fun k => equivShrink M (q k)) 1,
      L.limitCarrier.metricComplete (L.limitFlow.metric 0) := by
  classical
  let H := G.unscaledCompactnessHypotheses q (-1) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨σ, hσ, R, ρ, a, b, N, hparams, hcovers⟩ :=
    H.exists_diagonal_normalChartCovers (by omega)
  let seq := H.sequence.subsequence σ
  let cover : ∀ k j, j ≤ k → NormalChartCover (seq.flow k).flow.metric
      (seq.flow k).base (-1) (1 / 2) ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j) :=
    fun k j hjk => (hcovers k j hjk).choose
  have hraw : ∀ i : ℕ,
      let raw := fun k (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
        ((seq.flow k).flow.metric z.1).pullbackCoefficients
          ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
            ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
              Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2
      LocallyEventuallyContDiff (Iio 1 ×ˢ Metric.ball 0 (ρ (Nat.unpair i).1)) raw ∧
      (∀ K : Set (ℝ × EuclideanSpace ℝ (Fin 3)), IsCompact K →
        K ⊆ Iio 1 ×ˢ Metric.ball 0 (ρ (Nat.unpair i).1) → ∀ d : ℕ, ∃ B : ℝ,
          ∀ᶠ k in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ d (raw k) z‖ ≤ B) ∧
      (∀ t ∈ Iio 1, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
        ∀ x ∈ Metric.ball 0 (ρ (Nat.unpair i).1), ∀ v,
          c * ‖v‖ ^ 2 ≤ raw k (t, x) v v) := by
    intro i
    let j := (Nat.unpair i).1
    let l : Fin (N j + 1) :=
      ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    let rawStage := fun k j (hk : j ≤ k) (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
      ((seq.flow k).flow.metric z.1).pullbackCoefficients
        ((cover k j hk).chart
          ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2
    let raw := fun k => rawStage k (min j k) (min_le_right _ _)
    change LocallyEventuallyContDiff (Iio 1 ×ˢ Metric.ball 0 (ρ j)) raw ∧ _
    have hstage (k : ℕ) (hk : j ≤ k) : raw k =
        fun z => ((seq.flow k).flow.metric z.1).pullbackCoefficients
          ((cover k j hk).chart l) z.2 := by
      funext z
      change rawStage k (min j k) (min_le_right _ _) z = rawStage k j hk z
      simp only [min_eq_left hk]
    refine ⟨?_, ?_, ?_⟩
    · intro K hK hKΩ
      have hKI : Prod.fst '' K ⊆ Iio 1 := by
        rintro t ⟨z, hz, rfl⟩
        exact (hKΩ hz).1
      obtain ⟨s, t, hs, ht, ht1, htime⟩ := compact_time_window (hK.image continuous_fst) hKI
      let W := G.unscaledCompactnessHypotheses (q ∘ σ) s t hs ht ht1
      filter_upwards [eventually_ge_atTop j] with k hkj
      refine ⟨Ioo s t ×ˢ Metric.ball 0 (R j), isOpen_Ioo.prod Metric.isOpen_ball, ?_, ?_⟩
      · intro z hz
        exact ⟨htime (mem_image_of_mem Prod.fst hz),
          Metric.ball_subset_ball (by linarith [(hparams j).1, (hparams j).2.1])
            (hKΩ hz).2⟩
      · rw [hstage k hkj]
        exact W.referenceNormalChartCover_contDiffOn k (cover k j hkj) l
    · intro K hK hKΩ d
      have hKI : Prod.fst '' K ⊆ Iio 1 := by
        rintro t ⟨z, hz, rfl⟩
        exact (hKΩ hz).1
      obtain ⟨s, t, hs, ht, ht1, htime⟩ := compact_time_window (hK.image continuous_fst) hKI
      let W := G.unscaledCompactnessHypotheses (q ∘ σ) s t hs ht ht1
      obtain ⟨B, _, hjets⟩ := W.eventually_referenceNormalChartCover_spacetime_jet_bound
        hC.local_derivative_estimates_small H.time_bounds (hK.image continuous_fst) htime
        (N := N j) (by positivity : 0 < (j : ℝ) + 1)
        (hparams j).1 (hparams j).2.1 (hparams j).2.2.1 (hparams j).2.2.2 d
      refine ⟨B, ?_⟩
      filter_upwards [hjets, eventually_ge_atTop j] with k hk hkj
      intro z hz
      change ‖iteratedFDeriv ℝ d (raw k) z‖ ≤ B
      rw [hstage k hkj]
      exact hk (cover k j hkj) l z.1 (mem_image_of_mem Prod.fst hz) z.2
        (Metric.ball_subset_closedBall (hKΩ hz).2)
    · intro t ht
      obtain ⟨s, b', hs, hb', hb1, htime⟩ :=
        compact_time_window isCompact_singleton (singleton_subset_iff.mpr ht)
      let W := G.unscaledCompactnessHypotheses (q ∘ σ) s b' hs hb' hb1
      obtain ⟨c, d, hc, _, helliptic⟩ := W.eventually_referenceNormalChartCover_ellipticity
        H.time_bounds (N := N j) (by positivity : 0 < (j : ℝ) + 1)
        (hparams j).1 (hparams j).2.1 (hparams j).2.2.1 (hparams j).2.2.2
      refine ⟨c, hc, ?_⟩
      filter_upwards [helliptic, eventually_ge_atTop j] with k hk hkj
      intro x hx v
      change c * ‖v‖ ^ 2 ≤ raw k (t, x) v v
      rw [hstage k hkj]
      exact (hk (cover k j hkj) l t (htime (mem_singleton t)) x
        (Metric.closedBall_subset_closedBall (by linarith [(hparams j).1])
          (Metric.ball_subset_closedBall hx)) v).1
  let Fseq (k : ℕ) : RicciFlow 3 (seq.carrier k).carrier (Iio 1) :=
    G.unscaledSourceFlow.shrink
  have htime : ∀ s t : ℝ, t < 1 → ∀ᶠ _k : ℕ in atTop, Icc s t ⊆ Iio 1 := by
    intro s t ht
    exact Filter.Eventually.of_forall fun _ _ hx => hx.2.trans_lt ht
  obtain ⟨L, hL⟩ := NormalChartCover.exists_complete_ancient_geometric_limit
    Fseq (fun _ => rfl) (by norm_num : (0 : ℝ) < 1) htime cover
    (fun j => (hparams j).1)
    (fun j => by linarith [(hparams j).1, (hparams j).2.1])
    (fun j => (hparams j).2.2.1) hraw
  exact ⟨L.ofSubsequence hσ, hL⟩

variable {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)


theorem unscaledPointedLimit_curvature_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, t < 1 → ∀ x : L.limitCarrier.carrier,
      (L.limitFlow.connection t).curvatureTensorNorm x ≤ B / (1 - t) := by
  obtain ⟨B, hB, hbound⟩ := G.unscaledSourceFlow_curvature_bound
  refine ⟨B, hB, fun t ht x => ?_⟩
  obtain ⟨a, b, ha, hb, hb1, htime⟩ :=
    compact_time_window isCompact_singleton (singleton_subset_iff.mpr ht)
  let W := L.window (J := fun _ => Iio 1)
    (C := fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink) (ha.trans hb) hb1.le 0
    (fun _ _ hs => hs.2.trans hb1)
  apply le_of_tendsto (W.tendsto_curvatureTensorNorm t (htime (mem_singleton t)) x)
  apply Filter.Eventually.of_forall
  intro k
  change (G.unscaledSourceFlow.shrink.connection t).curvatureTensorNorm _ ≤ B / (1 - t)
  rw [RicciFlow.shrink_curvatureTensorNorm]
  exact (le_abs_self _).trans (hbound t ht _)

theorem unscaledPointedLimit_nonnegativeCurvatureOperator :
    ∀ t : ℝ, t < 1 → ∀ x : L.limitCarrier.carrier,
      (L.limitFlow.connection t).NonnegativeCurvatureOperator x := by
  apply AncientPointedGeometricConvergence.nonnegativeCurvatureOperator_of_eventually
    (C := fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (J := fun _ => Iio 1) (fun _ => G.unscaledSourceFlow.shrink) L
    (by norm_num : (0 : ℝ) < 1)
    (fun a b hb => Filter.Eventually.of_forall fun _ _ ht => ht.2.trans_lt hb)
  intro t ht
  apply Filter.Eventually.of_forall
  intro k x
  exact (G.unscaledSourceFlow.shrink_nonnegativeCurvatureOperator_iff t x).mpr
    (G.unscaledSourceFlow_nonnegativeCurvatureOperator t ht _)



theorem unscaledPointedLimit_complete
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0)) :
    ∀ t : ℝ, t < 1 → L.limitCarrier.metricComplete (L.limitFlow.metric t) := by
  obtain ⟨B, hB, hbound⟩ := G.unscaledPointedLimit_curvature_bound L
  intro t ht
  obtain ⟨a, b, ha, hb, hb1, htime⟩ :=
    compact_time_window isCompact_singleton (singleton_subset_iff.mpr ht)
  let W := L.limitCarrier.basedWindow L.limitFlow L.base
    (fun _ hs => hs.2.trans hb1 : Ioo a b ⊆ Iio 1) (ha.trans hb)
  apply W.complete_interior_of_two_time_curvature_bound ⟨ha, hb⟩ hcomplete ?_
    t (htime (mem_singleton t))
  intro A _
  refine ⟨B / (1 - b), div_nonneg hB (sub_pos.mpr hb1).le, ?_⟩
  intro s _ u hu x _
  exact (hbound u (hu.2.trans hb1) x).trans
    (div_le_div_of_nonneg_left hB (sub_pos.mpr hb1) (by linarith [hu.2]))

end PoincareConjecture.ShrinkingSolitonFlow
