import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.AncientReselect


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem reducedLengthPullback_limit_lipschitz_on_chart_cylinder
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier)
    {a : EuclideanSpace ℝ (Fin n)} {r α β : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β)
    (hchart : Metric.closedBall a (2 * r) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∃ D : ℝ≥0, LipschitzOnWith D
      (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
        l ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1, z.2))
      (Metric.closedBall a r ×ˢ Icc α β) := by
  obtain ⟨D, C, hC, hg⟩ := G.reducedLengthPullback_eventually_lipschitz_on_chart_cylinder
    P q hr hα hαβ hchart
  refine ⟨D, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro z hz w hw
  have hzlim := hlim.tendsto_at (show
    ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1, z.2) ∈ univ ×ˢ Ioi (0 : ℝ)
      from ⟨mem_univ _, hα.trans_le hz.2.1⟩)
  have hwlim := hlim.tendsto_at (show
    ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm w.1, w.2) ∈ univ ×ˢ Ioi (0 : ℝ)
      from ⟨mem_univ _, hα.trans_le hw.2.1⟩)
  apply le_of_tendsto (hzlim.dist hwlim)
  filter_upwards [hσ.tendsto_atTop.eventually hg] with k hk
  exact hk.1.dist_le_mul z hz w hw

theorem reducedLengthPullback_limit_coordinates_locallyLipschitz
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) :
    LocallyLipschitzOn ((chartAt (EuclideanSpace ℝ (Fin n)) q).target ×ˢ Ioi (0 : ℝ))
      (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
        l ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1, z.2)) := by
  intro z hz
  have hzpos : 0 < z.2 := hz.2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (chartAt (EuclideanSpace ℝ (Fin n)) q).open_target z.1 hz.1
  have hchart : Metric.closedBall z.1 (2 * (r / 4)) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) q).target := by
    intro x hx
    apply hball
    change dist x z.1 < r
    have hd : dist x z.1 ≤ 2 * (r / 4) := hx
    linarith
  obtain ⟨D, hD⟩ := G.reducedLengthPullback_limit_lipschitz_on_chart_cylinder P hσ l hlim q
    (show 0 < r / 4 by positivity) (show 0 < z.2 / 2 by linarith)
    (show z.2 / 2 ≤ z.2 + 1 by linarith) hchart
  refine ⟨D, Metric.closedBall z.1 (r / 4) ×ˢ Icc (z.2 / 2) (z.2 + 1), ?_, hD⟩
  exact mem_nhdsWithin_of_mem_nhds (prod_mem_nhds
    (Metric.closedBall_mem_nhds z.1 (by positivity))
    (Icc_mem_nhds (by linarith) (by linarith)))

theorem exists_reducedLengthPullback_locallyLipschitz_limit
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K) :
    ∃ σ : ℕ → ℕ, ∃ hσ : StrictMono σ, ∃ l : G.limit.carrier.carrier × ℝ → ℝ,
      ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)) ∧
      TendstoLocallyUniformlyOn
        (fun k z => (G.reselect σ hσ).reducedLengthPullback k z.1 z.2)
        l atTop (univ ×ˢ Ioi (0 : ℝ)) ∧
      (∀ A : Set (G.limit.carrier.carrier × ℝ), IsCompact A → A ⊆ univ ×ˢ Ioi (0 : ℝ) →
        TendstoUniformlyOn
          (fun k z => (G.reselect σ hσ).reducedLengthPullback k z.1 z.2) l atTop A) ∧
      ∀ q : G.limit.carrier.carrier,
        LocallyLipschitzOn ((chartAt (EuclideanSpace ℝ (Fin n)) q).target ×ˢ Ioi (0 : ℝ))
          (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
            l ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1, z.2)) := by
  obtain ⟨σ, hσ, l, hl, hlim⟩ := G.exists_reducedLengthPullback_locallyUniform_limit P
  refine ⟨σ, hσ, l, hl, hlim, ?_, ?_⟩
  · intro A hA hsub
    exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hA).mp (hlim.mono hsub)
  · exact G.reducedLengthPullback_limit_coordinates_locallyLipschitz P hσ l hlim

end PoincareConjecture.AncientCompactTimeConvergence
