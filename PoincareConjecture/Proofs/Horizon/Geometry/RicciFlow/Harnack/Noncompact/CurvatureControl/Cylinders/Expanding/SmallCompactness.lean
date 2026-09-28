import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.GeometricLimit.NormalCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.DiagonalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.SmallChartBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Source

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

attribute [local instance] smallCarrier smallChartedSpace smallIsManifold

theorem exists_complete_ancient_limit_of_small_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
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
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
        (fun k t => (F k).shrink.metric (t - δ))
        (fun k => equivShrink (C k).carrier (p k)) δ,
      G.limitCarrier.metricComplete (G.limitFlow.metric 0) := by
  classical
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hA.eventually_ge_atTop 2)
  have hsub (k : ℕ) : Icc (-2 : ℝ) 0 ⊆ Icc (-A (k + k₀)) 0 :=
    Icc_subset_Icc (by linarith [hk₀ (k + k₀) (Nat.le_add_left k₀ k)]) le_rfl
  have hJ₀ : ∀ k, Icc (-2 : ℝ) 0 ⊆ interior (J (k + k₀)) :=
    fun k _ ht => hJ (k + k₀) (hsub k ht)
  have htail : Tendsto (fun k : ℕ => k + k₀) atTop atTop := tendsto_add_atTop_nat k₀
  obtain ⟨H₀, hseq⟩ := exists_pointedCompactnessHypotheses_of_small_terminal_cylinders
    hC hm (fun k => C (k + k₀)) (fun k => J (k + k₀))
    (fun k => F (k + k₀)) (fun k => p (k + k₀)) (by norm_num : (-2 : ℝ) ≤ -1)
    hδ hδone.le (by linarith) hJ₀
    (fun k t ht => hcomplete (k + k₀) t (hsub k ht))
    (fun k t ht x => hoperator (k + k₀) t (hsub k ht) x)
    (fun k => L (k + k₀)) (hL.comp htail)
    (fun k t ht x hx => hscalar (k + k₀) t (hsub k ht) x hx)
    hν (htail.eventually hvolume)
  rcases H₀ with ⟨hT, seq, hvol, hcompact, hspace, hall, hnoncollapse⟩
  dsimp only at hseq
  subst seq
  let H : PointedRicciFlowCompactnessHypotheses (m + 1) (-2 + δ) δ :=
    ⟨hT, smallBufferedCylinderSequence (fun k => C (k + k₀)) (fun k => J (k + k₀))
      (fun k => F (k + k₀)) (fun k => p (k + k₀)) (-2) δ (by norm_num) hJ₀,
      hvol, hcompact, hspace, hall, hnoncollapse⟩
  obtain ⟨σ, hσ, R, ρ, a, b, N, hparams, hcovers⟩ :=
    H.exists_diagonal_normalChartCovers (by omega)
  let S := H.sequence.subsequence σ
  let φ := fun k => σ k + k₀
  have hφ : StrictMono φ := fun i j hij => Nat.add_lt_add_right (hσ hij) k₀
  let cover : ∀ k j, j ≤ k → NormalChartCover (S.flow k).flow.metric
      (S.flow k).base (-2 + δ) δ ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j) :=
    fun k j hjk => (hcovers k j hjk).choose
  have hraw := diagonal_referenceCharts_analytic_bounds_of_estimates
    (δ := δ) S hparams cover (by
      intro j I hIcompact hI
      obtain ⟨s, a', b', hs, htime, ha', hb', hsmooth, hjets⟩ :=
        eventually_referenceChart_estimates_of_small_expanding_cylinders
          hC hm (fun k => C (φ k)) (fun k => J (φ k)) (fun k => F (φ k))
          (fun k => p (φ k)) (fun k => A (φ k)) (fun k => L (φ k))
          (hA.comp hφ.tendsto_atTop) (hL.comp hφ.tendsto_atTop)
          (fun k => hJ (φ k)) (fun k => hcomplete (φ k))
          (fun k => hoperator (φ k)) (fun k => hscalar (φ k))
          hν (hφ.tendsto_atTop.eventually hvolume) hδ hδone H.time_bounds
          (by positivity : 0 < (j : ℝ) + 1) (hparams j).1
          (hparams j).2.1 (hparams j).2.2.1 (hparams j).2.2.2
          (N := N j) hIcompact hI
      refine ⟨s, a', htime, ha', ?_, ?_⟩
      · filter_upwards [hsmooth] with k hk
        intro hjk i
        exact ⟨(hk (cover k j hjk) i).1,
          fun t ht x hx v => ((hk (cover k j hjk) i).2 t ht x hx v).1⟩
      · intro d
        obtain ⟨B, _, hbound⟩ := hjets d
        refine ⟨B, ?_⟩
        filter_upwards [hbound] with k hk
        exact fun hjk => hk (cover k j hjk))
  let Fseq (k : ℕ) : RicciFlow (m + 1) (S.carrier k).carrier
      ((fun t : ℝ => t - δ) ⁻¹' J (φ k)) := (F (φ k)).shrink.bufferedExpandingFlow δ
  have htime : ∀ s t : ℝ, t < δ → ∀ᶠ k in atTop,
      Icc s t ⊆ (fun u : ℝ => u - δ) ⁻¹' J (φ k) := by
    intro s t ht
    exact hφ.tendsto_atTop.eventually (eventually_buffered_time_window J A hA hJ δ s t ht)
  obtain ⟨G, hG⟩ := NormalChartCover.exists_complete_ancient_geometric_limit
    Fseq (fun _ => rfl) hδ htime cover (fun j => (hparams j).1)
    (fun j => by linarith [(hparams j).1, (hparams j).2.1])
    (fun j => (hparams j).2.2.1) hraw
  exact ⟨G.ofSubsequence hφ, hG⟩

end PoincareConjecture.RicciFlow
