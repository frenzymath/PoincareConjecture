import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Terminal.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.LimitScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.smallCarrier RicciFlow.smallChartedSpace RicciFlow.smallIsManifold

theorem exists_ancient_terminal_epsilonNeck_threshold
    (hC : RicciFlowCurvatureTheory.{u}) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (C : ℕ → FlowCarrier.{u} 3) (I : ℕ → Set ℝ)
        (F : ∀ k, RicciFlow 3 (C k).carrier (I k))
        (p : ∀ k, (C k).carrier) (A radius : ℕ → ℝ),
        Tendsto A atTop atTop → Tendsto radius atTop atTop →
        (∀ k, IsOpen (I k)) →
        (∀ k, Icc (-A k) 0 ⊆ interior (I k)) →
        (∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t)) →
        (∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
          ((F k).connection t).NonnegativeCurvatureOperator x) →
        (∀ k, ∀ t ∈ Icc (-A k) 0,
          ∀ x ∈ ((F k).metric 0).ball (p k) (radius k),
            ((F k).connection t).scalarCurvature x ≤ 4) →
        (∀ k, ((F k).connection 0).scalarCurvature (p k) = 1) →
        (∀ k, ∀ t ∈ Icc (-A k) 0, ((F k).connection t).scalarCurvature (p k) ≤ 1) →
      ∀ {δ : ℝ}, 0 < δ → δ ≤ η →
      ∀ G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
        (fun k t => (F k).shrink.metric (t - δ))
        (fun k => equivShrink (C k).carrier (p k)) δ,
        G.limitCarrier.metricComplete (G.limitFlow.metric 0) →
      ∀ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
        (q : UnitTwoSphere), Φ (q, 0) = G.base →
        (fun z v w => (G.limitFlow.connection 0).scalarCurvature G.base *
          roundCylinderPullback (G.limitFlow.metric 0) Φ z v w) = EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop, ∃ N : EpsilonNeck ((F (G.subsequence i)).metric 0),
          N.epsilon = ε ∧ N.scale = 1 ∧ N.center = p (G.subsequence i) ∧
          N.connection = (F (G.subsequence i)).connection 0 ∧
          N.coordinate_map = (fun z => (equivShrink (C (G.subsequence i)).carrier).symm
            (G.embedding i (Φ z))) := by
  obtain ⟨D, hD, hscalarLimit⟩ :=
    RicciFlow.exists_buffered_limit_scalar_normalization_constant_universal hC
      (m := 2) (by norm_num)
  obtain ⟨θ, hθ, hneck⟩ :=
    PointedGeometricConvergence.exists_buffered_terminal_epsilonNeck_threshold
      hC hε hεhalf hD.le
  let η := min θ (min 1 (1 / (2 * D)))
  have hη : 0 < η := lt_min hθ (lt_min (by norm_num) (by positivity))
  refine ⟨η, hη, ?_⟩
  intro C I F p A radius hA hradius hopen hI hcomplete hoperator hscalar hnormalize
    hbase δ hδ hδη G hcompleteG Φ q hq hround
  have hδθ : δ ≤ θ := hδη.trans (min_le_left _ _)
  have hδone : δ ≤ 1 := hδη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδD : δ ≤ 1 / (2 * D) :=
    hδη.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hDδ : D * δ ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * D)).mp hδD
    nlinarith
  obtain ⟨hlo, hhi⟩ := hscalarLimit C I F p A radius hA hradius hI hcomplete hoperator
    hscalar hnormalize hbase hδ hδone G
  have hhalf : (1 / 2 : ℝ) ≤ (G.limitFlow.connection 0).scalarCurvature G.base := by
    linarith
  have hgap : 1 - (G.limitFlow.connection 0).scalarCurvature G.base ≤ D * δ := by
    linarith
  let Fsmall := fun k => (F k).shrink.bufferedExpandingFlow δ
  obtain ⟨a, b, ha, hb, hbδ, _⟩ := exists_ancient_window_of_isCompact hδ
    isCompact_singleton (singleton_subset_iff.mpr hδ)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually
      (RicciFlow.eventually_buffered_time_window I A hA hI δ a b hbδ))
  let W := window (C := fun k => (C k).shrink) Fsmall G (ha.trans hb) hbδ.le N hN
  let σ : ℕ → ℕ := fun k => G.subsequence (k + N)
  have hσ : Tendsto σ atTop atTop :=
    G.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat N)
  let Ψ := fun k => (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) (C (σ k)).carrier).symm
  have hresult := hneck W ⟨ha, hb⟩ hcompleteG Φ q hq (fun k => C (σ k))
    (fun k => I (σ k)) (fun k => F (σ k)) Ψ
    (A ∘ σ) (radius ∘ σ) (hA.comp hσ) (hradius.comp hσ)
    (fun k => hopen (σ k)) (fun k => hI (σ k))
    (fun k => hcomplete (σ k)) (fun k => hoperator (σ k))
    (fun k t ht x hx => hscalar (σ k) t ht x (by
      change x ∈ ((F (σ k)).metric 0).ball
        ((equivShrink (C (σ k)).carrier).symm
          (equivShrink (C (σ k)).carrier (p (σ k)))) (radius (σ k)) at hx
      simpa only [Equiv.symm_apply_apply] using hx))
    (fun k => by
      change ((F (σ k)).connection 0).scalarCurvature
        ((equivShrink (C (σ k)).carrier).symm
          (equivShrink (C (σ k)).carrier (p (σ k)))) = 1
      simpa only [Equiv.symm_apply_apply] using hnormalize (σ k))
    hδ hδone hδθ hhalf hhi hgap
    (fun k x v w => by
      change ((F (σ k)).shrink.metric (0 - δ)).inner x v w = _
      rw [zero_sub]
      rfl) hround
  have htail : ∀ᶠ i in atTop,
      ∃ N' : EpsilonNeck ((F (G.subsequence (i + N))).metric 0),
        N'.epsilon = ε ∧ N'.scale = 1 ∧ N'.center = p (G.subsequence (i + N)) ∧
        N'.connection = (F (G.subsequence (i + N))).connection 0 ∧
        N'.coordinate_map =
          (fun z => (equivShrink (C (G.subsequence (i + N))).carrier).symm
            (G.embedding (i + N) (Φ z))) := by
    filter_upwards [hresult] with i hi
    obtain ⟨N', hε', hscale, hcenter, hconnection, hmap, _, _⟩ := hi
    refine ⟨N', hε', hscale, ?_, hconnection, hmap⟩
    change N'.center = (equivShrink (C (G.subsequence (i + N))).carrier).symm
      (equivShrink (C (G.subsequence (i + N))).carrier (p (G.subsequence (i + N))))
      at hcenter
    simpa only [Equiv.symm_apply_apply] using hcenter
  rw [← map_add_atTop_eq_nat N]
  exact htail

end PoincareConjecture.AncientPointedGeometricConvergence
