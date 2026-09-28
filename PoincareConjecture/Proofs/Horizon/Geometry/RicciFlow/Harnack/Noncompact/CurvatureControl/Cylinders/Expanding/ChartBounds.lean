import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Compactness
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Eventual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem eventually_referenceChart_estimates_of_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{0} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1))
    {δ S' S r R ρ a b : ℝ} {N : ℕ} (hδ : 0 < δ) (hδone : δ < 1)
    (hS : S' < 0 ∧ 0 < S) (hr : 0 < r) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 < b)
    {I : Set ℝ} (hIcompact : IsCompact I) (hI : I ⊆ Iio δ) :
    ∃ T' a' b' : ℝ, T' < 0 ∧ I ⊆ Ioo T' δ ∧ 0 < a' ∧ 0 < b' ∧
      (∀ᶠ k in atTop,
        ∀ cover : NormalChartCover (fun t => (F k).metric (t - δ))
            (p k) S' S r R ρ a b N,
          ∀ i,
            ContDiffOn ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
              ((F k).metric (z.1 - δ)).pullbackCoefficients (cover.chart i) z.2)
              (Ioo T' δ ×ˢ Metric.ball 0 R) ∧
            ∀ t ∈ Ioo T' δ, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ v,
              a' * ‖v‖ ^ 2 ≤ ((F k).metric (t - δ)).pullbackCoefficients
                  (cover.chart i) x v v ∧
              ((F k).metric (t - δ)).pullbackCoefficients (cover.chart i) x v v ≤
                b' * ‖v‖ ^ 2) ∧
      ∀ d : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
        ∀ cover : NormalChartCover (fun t => (F k).metric (t - δ))
            (p k) S' S r R ρ a b N,
          ∀ i, ∀ t ∈ I, ∀ x ∈ Metric.closedBall 0 ρ,
            ‖iteratedFDeriv ℝ d (fun z : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
              ((F k).metric (z.1 - δ)).pullbackCoefficients (cover.chart i) z.2)
              (t, x)‖ ≤ B := by
  obtain ⟨l, hl⟩ := hIcompact.bddBelow
  let q := min (-2) (l - δ - 1)
  have hq : q ≤ -2 := min_le_left _ _
  have hqI : I ⊆ Ioo (q + δ) δ := by
    intro t ht
    refine ⟨?_, hI ht⟩
    have hqt : q ≤ l - δ - 1 := min_le_right _ _
    linarith [hl ht]
  obtain ⟨j, hj⟩ := eventually_atTop.mp (hA.eventually_ge_atTop (-q))
  have hsub (k : ℕ) : Icc q 0 ⊆ Icc (-A (k + j)) 0 :=
    Icc_subset_Icc (by linarith [hj (k + j) (Nat.le_add_left j k)]) le_rfl
  have hJj : ∀ k, Icc q 0 ⊆ interior (J (k + j)) :=
    fun k _ ht => hJ (k + j) (hsub k ht)
  have htail : Tendsto (fun k : ℕ => k + j) atTop atTop := tendsto_add_atTop_nat j
  obtain ⟨H, hHS⟩ := exists_pointedCompactnessHypotheses_of_terminal_cylinders
    hC hm (fun k => C (k + j)) (fun k => J (k + j))
    (fun k => F (k + j)) (fun k => p (k + j)) (by linarith : q ≤ -1)
    hδ hδone.le (by linarith) hJj
    (fun k t ht => hcomplete (k + j) t (hsub k ht))
    (fun k t ht x => hoperator (k + j) t (hsub k ht) x)
    (fun k => L (k + j)) (hL.comp htail)
    (fun k t ht x hx => hscalar (k + j) t (hsub k ht) x hx)
    hν (htail.eventually hvolume)
  obtain ⟨a', b', ha', hb', helliptic⟩ :=
    H.eventually_referenceNormalChartCover_ellipticity hS (N := N) hr hρ hρR ha hb
  have hsmooth := H.referenceNormalChartCover_contDiffOn (S' := S') (S := S)
    (A := r) (R := R) (ρ := ρ) (a := a) (b := b) (N := N)
  have hjets (d : ℕ) := H.eventually_referenceNormalChartCover_spacetime_jet_bound
    hC.local_derivative_estimates hS hIcompact hqI (N := N) hr hρ hρR ha hb d
  rcases H with ⟨hT, seq, hvol, hcompact, hspace, hall, hnoncollapse⟩
  dsimp only at hHS
  subst seq
  refine ⟨q + δ, a', b', by linarith, hqI, ha', hb', ?_, ?_⟩
  · rw [← map_add_atTop_eq_nat j]
    apply eventually_map.mpr
    filter_upwards [helliptic] with k hk
    intro cover i
    exact ⟨hsmooth k cover i, hk cover i⟩
  · intro d
    obtain ⟨B, hB, hbound⟩ := hjets d
    refine ⟨B, hB, ?_⟩
    rw [← map_add_atTop_eq_nat j]
    exact eventually_map.mpr hbound

theorem referenceCharts_analytic_bounds_of_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{0} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1))
    {δ S' S r R ρ a b : ℝ} {N : ℕ} (hδ : 0 < δ) (hδone : δ < 1)
    (hS : S' < 0 ∧ 0 < S) (hr : 0 < r) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (ha : 0 < a) (hb : 0 < b)
    (cover : ∀ k, NormalChartCover (fun t => (F k).metric (t - δ))
      (p k) S' S r R ρ a b N) :
    ∀ i : Fin (N + 1),
      Poincare.Analysis.Calculus.LocallyEventuallyContDiff
        (Iio δ ×ˢ Metric.ball 0 ρ)
        (fun k (z : ℝ × EuclideanSpace ℝ (Fin (m + 1))) =>
          ((F k).metric (z.1 - δ)).pullbackCoefficients ((cover k).chart i) z.2) ∧
      (∀ d : ℕ, ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin (m + 1))),
        IsCompact K → K ⊆ Iio δ ×ˢ Metric.ball 0 ρ →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ z ∈ K,
          ‖iteratedFDeriv ℝ d (fun w : ℝ × EuclideanSpace ℝ (Fin (m + 1)) =>
            ((F k).metric (w.1 - δ)).pullbackCoefficients ((cover k).chart i) w.2) z‖ ≤ B) ∧
      (∀ t ∈ Iio δ, ∀ x ∈ Metric.ball 0 ρ, ∃ a' : ℝ, 0 < a' ∧ ∀ᶠ k in atTop,
        ∀ v, a' * ‖v‖ ^ 2 ≤ ((F k).metric (t - δ)).pullbackCoefficients
          ((cover k).chart i) x v v) := by
  intro i
  have estimates {I : Set ℝ} (hIcompact : IsCompact I) (hI : I ⊆ Iio δ) :=
    eventually_referenceChart_estimates_of_expanding_cylinders
    hC hm C J F p A L hA hL hJ hcomplete hoperator hscalar hν hvolume
    hδ hδone hS hr hρ hρR ha hb (N := N) hIcompact hI
  refine ⟨?_, ?_, ?_⟩
  · intro K hK hKΩ
    have hKI : Prod.fst '' K ⊆ Iio δ := by
      rintro t ⟨z, hz, rfl⟩
      exact (hKΩ hz).1
    obtain ⟨T', a', b', hT', htime, ha', hb', hsmooth, _⟩ :=
      estimates (hK.image continuous_fst) hKI
    filter_upwards [hsmooth] with k hk
    refine ⟨Ioo T' δ ×ˢ Metric.ball 0 R, isOpen_Ioo.prod Metric.isOpen_ball, ?_,
      (hk (cover k) i).1⟩
    intro z hz
    exact ⟨htime (mem_image_of_mem Prod.fst hz),
      Metric.ball_subset_ball (by linarith) (hKΩ hz).2⟩
  · intro d K hK hKΩ
    have hKI : Prod.fst '' K ⊆ Iio δ := by
      rintro t ⟨z, hz, rfl⟩
      exact (hKΩ hz).1
    obtain ⟨T', a', b', hT', htime, ha', hb', hsmooth, hjets⟩ :=
      estimates (hK.image continuous_fst) hKI
    obtain ⟨B, hB, hbound⟩ := hjets d
    refine ⟨B, hB, ?_⟩
    filter_upwards [hbound] with k hk
    intro z hz
    exact hk (cover k) i z.1 (mem_image_of_mem Prod.fst hz) z.2
      (Metric.ball_subset_closedBall (hKΩ hz).2)
  · intro t ht x hx
    obtain ⟨T', a', b', hT', htime, ha', hb', hbound, _⟩ :=
      estimates isCompact_singleton (singleton_subset_iff.mpr ht)
    refine ⟨a', ha', ?_⟩
    filter_upwards [hbound] with k hk
    intro v
    exact ((hk (cover k) i).2 t (htime (mem_singleton t)) x
      (Metric.closedBall_subset_closedBall (by linarith)
        (Metric.ball_subset_closedBall hx)) v).1

end PoincareConjecture.RicciFlow
