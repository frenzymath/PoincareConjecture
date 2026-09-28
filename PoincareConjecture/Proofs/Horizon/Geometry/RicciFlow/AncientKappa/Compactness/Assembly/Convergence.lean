import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.TerminalConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.TimeShift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Embeddings
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.TimeWindows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance assemblyConvergenceCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)

def compactnessTimeWindow (j : ℕ) : Set ℝ := ancientM18TimeWindow (j + 1)

theorem compactnessTimeWindow_interval (j : ℕ) :
    ∃ a b : ℝ, a < b ∧ compactnessTimeWindow j = Icc a b := by
  refine ⟨-(((j + 1 : ℕ) : ℝ) + 1), -(((j + 1 : ℕ) : ℝ) + 1)⁻¹, ?_, rfl⟩
  have hd : 1 < ((j + 1 : ℕ) : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) j
    push_cast
    linarith
  have hi : (((j + 1 : ℕ) : ℝ) + 1)⁻¹ < 1 :=
    (inv_lt_one₀ (by linarith : 0 < ((j + 1 : ℕ) : ℝ) + 1)).2 hd
  linarith

theorem compactnessTimeWindow_covers : ⋃ j, compactnessTimeWindow j = Iio 0 := by
  apply Subset.antisymm
  · exact iUnion_subset (fun j => ancientM18TimeWindow_subset (j + 1))
  · intro t ht
    rw [← ancientM18TimeWindow_covers] at ht
    obtain ⟨j, hj⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨j, ancientM18TimeWindow_increasing j hj⟩

theorem interiorLimit_pullback_metric_CInfinity_within_Icc
    (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
    (hF : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1))
    (l u : ℝ) (hlu : l < u) (hu : u < 0)
    (q : G.limitCarrier.carrier) (j r : ℕ)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {z | z.1 ∈ Icc l u ∧ z.2 ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ G.exhaustion j})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ a b : Fin 3, ∀ z ∈ K,
      ‖iteratedFDerivWithin ℝ r
          (G.limitCarrier.coordinateCoefficient q
            (fun t x v w => spatialPullbackInner G.limitCarrier
              (S.term (G.subsequence k)).carrier
              ((S.term (G.subsequence k)).flow.flow.metric t)
              (G.embedding k) x v w) a b) (Icc l u ×ˢ Set.univ) z -
        iteratedFDerivWithin ℝ r
          (G.limitCarrier.coordinateCoefficient q
            (fun t x v w => (F.metric t).inner x v w) a b)
          (Icc l u ×ˢ Set.univ) z‖ < ε := by
  have hg : ∀ k, RiemannianMetric.IsSmoothFamilyOn
      (fun t => (S.term k).flow.flow.metric ((t + 1) - 1)) (Iio (1 - 1 : ℝ)) := by
    intro k
    simp only [add_sub_cancel_right, sub_self]
    exact (S.term k).flow.flow.smooth.mono (prod_mono_left Iio_subset_Iic_self)
  obtain ⟨N, hjN, hN⟩ := (G.translate 1).pullback_metric_CInfinity_within_Icc
    hg l u hlu (by simpa only [sub_self] using hu) q j r K hK hKU ε hε
  refine ⟨N, hjN, fun k hk a b z hz => ?_⟩
  have hNk := hN k hk a b z hz
  have heq : EqOn
      (G.limitCarrier.coordinateCoefficient q
        (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metric (t + 1))
          x v w) a b)
      (G.limitCarrier.coordinateCoefficient q
        (fun t x v w => (F.metric t).inner x v w) a b)
      (Icc l u ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 3)))) := by
    intro y hy
    change (G.limitFlow.metric (y.1 + 1)).inner _ _ _ = (F.metric y.1).inner _ _ _
    rw [hF y.1 (hy.1.2.trans_lt hu)]
  have hmem : z ∈ Icc l u ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 3))) :=
    ⟨(hKU hz).1, mem_univ _⟩
  rw [← iteratedFDerivWithin_congr heq hmem r]
  simpa only [AncientPointedGeometricConvergence.translate, RicciFlow.translate_metric,
    add_sub_cancel_right] using hNk

variable (K : AncientKappaSolution 3 G.limitCarrier.carrier)
  (hκ : K.kappa = κ)
  (hnormalized : (K.flow.connection 0).scalarCurvature G.base = 1)

def retainedBasedLimit : BasedKappaSolution κ where
  carrier := G.limitCarrier
  connectedSpace := inferInstance
  flow := K
  base := G.base
  kappa_eq := hκ
  scalar_normalized := hnormalized

noncomputable def retainedSpacetimeEmbedding (j : ℕ) (J : Set ℝ) :
    NormalizedKappaSpacetimeEmbedding
      (source := S.term (G.subsequence j))
      (target := S.retainedBasedLimit G K hκ hnormalized) (J ×ˢ G.exhaustion j) :=
  NormalizedKappaSpacetimeEmbedding.of_spatial (G.exhaustion_open j) (G.embedding j)
    (by
      intro x hx y hy hxy
      have hxy' : (⟨x, hx⟩ : G.exhaustion j) = ⟨y, hy⟩ :=
        (G.embedding_open j).injective hxy
      exact congrArg Subtype.val hxy') (G.embedding_smooth j) J

noncomputable def retainedInteriorConvergence
    (hK : ∀ t : ℝ, t < 0 → K.flow.metric t = G.limitFlow.metric (t + 1)) :
    M23InteriorConvergence S where
  limit := S.retainedBasedLimit G K hκ hnormalized
  subsequence := G.subsequence
  subsequence_strictMono := G.subsequence_strictMono
  exhaustion := G.exhaustion
  exhaustion_open := G.exhaustion_open
  exhaustion_connected := G.exhaustion_connected
  exhaustion_compactClosure := G.exhaustion_compactClosure
  exhaustion_increasing := G.exhaustion_increasing
  exhaustion_covers := G.exhaustion_covers
  time_window := compactnessTimeWindow
  time_window_interval := compactnessTimeWindow_interval
  time_window_compact := fun j => isCompact_ancientM18TimeWindow (j + 1)
  time_window_subset_ancient := fun j => ancientM18TimeWindow_subset (j + 1)
  time_window_increasing := fun j => ancientM18TimeWindow_increasing (j + 1)
  time_window_covers := compactnessTimeWindow_covers
  embedding := fun j => S.retainedSpacetimeEmbedding G K hκ hnormalized j
    (compactnessTimeWindow j)
  base_in_exhaustion := G.base_in_exhaustion
  base_preserving := fun j t _ => congrArg (Prod.mk t) (G.base_preserving j)
  pullback_metric_CInfinity := by
    dsimp only
    intro q j r L hL hLU ε hε
    obtain ⟨l, u, hlu, hwindow⟩ := compactnessTimeWindow_interval j
    have hu : u < 0 := ancientM18TimeWindow_subset (j + 1)
      (by change u ∈ compactnessTimeWindow j
          rw [hwindow]
          exact right_mem_Icc.mpr hlu.le)
    have hLU' : L ⊆ {z | z.1 ∈ Icc l u ∧ z.2 ∈ (extChartAt (𝓡 3) q).target ∧
        (extChartAt (𝓡 3) q).symm z.2 ∈ G.exhaustion j} := by
      simpa only [hwindow] using hLU
    obtain ⟨N, hjN, hN⟩ := S.interiorLimit_pullback_metric_CInfinity_within_Icc
      G K.flow hK l u hlu hu q j r L hL hLU' ε hε
    refine ⟨N, hjN, fun k hk a b z hz => ?_⟩
    rw [hwindow]
    exact hN k hk a b z hz

theorem retainedInteriorConvergence_terminalExtension
    (hK : ∀ t : ℝ, t < 0 → K.flow.metric t = G.limitFlow.metric (t + 1))
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    M23TerminalExtension (S.retainedInteriorConvergence G K hκ hnormalized hK) := by
  refine
    { endpoint_in_domain := by
        intro j
        change (0 : ℝ) ≤ 0 ∧ G.base ∈ G.exhaustion j
        exact ⟨le_rfl, G.base_in_exhaustion j⟩
      terminal_embedding := ?_
      complete_at_zero := K.complete 0 le_rfl
      bounded_at_zero := K.bounded_curvature 0 le_rfl
      noncollapsed_at_zero := ?_
      normalized_at_zero := hnormalized }
  · refine ⟨fun j => S.retainedSpacetimeEmbedding G K hκ hnormalized j (Iic 0),
      ?_, ?_, ?_⟩
    · intro j
      exact ⟨fun _ _ _ _ => rfl, congrArg (Prod.mk 0) (G.base_preserving j)⟩
    · intro j s t x _ _ _
      rfl
    · dsimp only [M23TerminalMetricConvergence]
      intro q j r L hL hLU ε hε
      exact S.terminal_pullback_metric_CInfinity G K.flow hK P hcontrol hcomplete
        q j r L hL hLU ε hε
  · dsimp only [M23TerminalNoncollapsing]
    intro r₀ hr₀ p r hr hrr hbound
    exact K.noncollapsed r₀ hr₀ 0 le_rfl p r hr hrr
      (by simpa only [zero_sub, retainedInteriorConvergence, retainedBasedLimit] using hbound)

include hκ hnormalized in

theorem exists_interiorConvergence_terminalExtension_of_ancient_limit
    (hK : ∀ t : ℝ, t < 0 → K.flow.metric t = G.limitFlow.metric (t + 1))
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    ∃ H : M23InteriorConvergence S, M23TerminalExtension H :=
  ⟨S.retainedInteriorConvergence G K hκ hnormalized hK,
    S.retainedInteriorConvergence_terminalExtension G K hκ hnormalized hK
      P hcontrol hcomplete⟩

end PoincareConjecture.NormalizedKappaSolutionSequence
