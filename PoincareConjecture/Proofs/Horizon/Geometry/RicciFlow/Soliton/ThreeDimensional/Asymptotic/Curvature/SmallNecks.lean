import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.RoundNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.CylinderNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Terminal.AncientNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Rescaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.Dichotomy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Euclidean

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  RicciFlow.smallCarrier RicciFlow.smallChartedSpace RicciFlow.smallIsManifold
  uliftSecondCountable uliftConnected

local instance smallNecksConnected {n : ℕ} (C : FlowCarrier n) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

set_option maxHeartbeats 1000000 in
theorem exists_small_neck_of_unbounded_scalarCurvature_of_euclidean
    (P : ThreeDimensionalClassificationPredecessors.{u})
    (L : AncientAsymptoticSolitonLimitData S)
    (d : L.convergence.limit.carrier.carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3))
    {t₀ : ℝ} (ht₀ : t₀ < 0)
    (hunbounded : ¬ BddAbove
      (range (L.convergence.limit.flow.connection t₀).scalarCurvature))
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N : EpsilonNeck
        ((L.convergence.limit.flow.ulift :
          RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0)).metric t₀),
      N.epsilon = ε ∧ N.scale < ρ := by
  obtain ⟨η, hη, hterminal⟩ :=
    AncientPointedGeometricConvergence.exists_ancient_terminal_epsilonNeck_threshold
      P.curvature hε hεhalf
  obtain ⟨q, r, hQ, hcontrol, _, hQt, hRt, _, _, hnormalize,
    _, _, _, δ, hδ, _, hδη, G, hcomplete, _, _, _, hmodel⟩ :=
    L.exists_scalar_normalized_round_surface_blowup_limit_of_unbounded_scalarCurvature
      P ht₀ L.convergence.limit.base hunbounded hη
  let F := L.convergence.limit.flow
  let V : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0) := F.ulift
  let Q := fun i => (F.connection t₀).scalarCurvature (q i)
  let R := fun i => r i * Real.sqrt (Q i)
  let H := fun i => V.openAncientRescaleAt (Q i) (hQ i) t₀
  obtain ⟨C, A, _, ⟨hround⟩, e, he, _⟩ := hmodel
  letI : CompactSpace C.carrier := hround.compact
  have hEuclidean : ∀ᶠ i : ℕ in atTop, Nonempty
      ((FlowCarrier.ofConnectedManifold 3
        (ULift.{u} L.convergence.limit.carrier.carrier)).shrink.carrier
          ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3)) :=
    Eventually.of_forall fun _ => ⟨
      (Poincare.Manifold.shrinkDiffeomorph (𝓡 3)
        (ULift.{u} L.convergence.limit.carrier.carrier)).symm.trans
        ((Poincare.Manifold.uliftDiffeomorph (𝓡 3)
          L.convergence.limit.carrier.carrier).trans d)⟩
  obtain ⟨_, Φ, x, hx, hnormalized⟩ :=
    G.exists_centered_scalarNormalized_roundCylinder_of_ulift_round_surface_product
      hEuclidean (A.flow.metric 0) (A.flow.connection 0)
      (hround.round_at_all_times 0 le_rfl) e (he 0 le_rfl)
  have htime (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i)) : t₀ + s / Q i < 0 := by
    have h := (div_lt_iff₀ (hQ i)).mpr hs
    linarith
  have hwindow (i : ℕ) (a : ℝ) : Icc a 0 ⊆ interior (Iio (-t₀ * Q i)) := by
    rw [isOpen_Iio.interior_eq]
    intro s hs
    exact hs.2.trans_lt (mul_pos (neg_pos.mpr ht₀) (hQ i))
  have hcompleteH (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i)) :
      MetricComplete ((H i).metric s) := by
    apply V.parabolicRescale_metricComplete
    exact (F.ulift_metricComplete_iff _).mpr (L.convergence.limit.complete _ (htime i s hs))
  have hoperatorH (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i))
      (y : ULift.{u} L.convergence.limit.carrier.carrier) :
      ((H i).connection s).NonnegativeCurvatureOperator y := by
    apply V.parabolicRescale_nonnegativeCurvatureOperator
    exact (F.ulift_nonnegativeCurvatureOperator_iff _ y).mpr
      (L.convergence.limit.nonnegative_curvature_operator _ (htime i s hs) y.down)
  have hball (i : ℕ) : ((H i).metric 0).ball (ULift.up (q i)) (R i) =
      (V.metric t₀).ball (ULift.up (q i)) (r i) := by
    change (rescaledMetric (V.metric (t₀ + 0 / Q i)) (Q i) (hQ i)).ball _ _ = _
    rw [rescaledMetric_ball_allDimensions, zero_div, add_zero]
    dsimp only [R]
    rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (hQ i)).ne']
  have hscalarH (i : ℕ) (s : ℝ) (hs : s ≤ 0)
      (y : ULift.{u} L.convergence.limit.carrier.carrier)
      (hy : y ∈ ((H i).metric 0).ball (ULift.up (q i)) (R i)) :
      ((H i).connection s).scalarCurvature y ≤ 4 := by
    have hst : t₀ + s / Q i ≤ t₀ :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)
    have hy' : y.down ∈ (F.metric t₀).ball (q i) (r i) := by
      have := (hball i) ▸ hy
      simpa only [RiemannianMetric.ball, Set.mem_ofPred_eq, V, F.ulift_edist] using this
    have hscalar := (L.convergence.limit.scalarCurvature_monotoneOn_of_derivative_nonnegative
      L.scalar_curvature_nonnegative_time_derivative y.down (hst.trans_lt ht₀) ht₀ hst).trans
        ((hcontrol i).2.1 y.down hy')
    dsimp only [H, RicciFlow.openAncientRescaleAt]
    rw [RicciFlow.parabolicRescale_scalarCurvature, F.ulift_scalarCurvature]
    exact (mul_le_mul_of_nonneg_left hscalar (inv_nonneg.mpr (hQ i).le)).trans_eq
      (by dsimp only [Q]; field_simp [(hQ i).ne'])
  have hbaseH (i : ℕ) (s : ℝ) (hs : s ≤ 0) :
      ((H i).connection s).scalarCurvature (ULift.up (q i)) ≤ 1 := by
    have hst : t₀ + s / Q i ≤ t₀ :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)
    have hscalar := L.convergence.limit.scalarCurvature_monotoneOn_of_derivative_nonnegative
      L.scalar_curvature_nonnegative_time_derivative (q i) (hst.trans_lt ht₀) ht₀ hst
    dsimp only [H, RicciFlow.openAncientRescaleAt]
    rw [RicciFlow.parabolicRescale_scalarCurvature, F.ulift_scalarCurvature]
    exact (mul_le_mul_of_nonneg_left hscalar (inv_nonneg.mpr (hQ i).le)).trans_eq
      (inv_mul_cancel₀ (hQ i).ne')
  let times : ℕ → ℝ := fun i => (i : ℝ) + 1
  have htimes : Tendsto times atTop atTop := tendsto_atTop_mono
    (fun i => show (i : ℝ) ≤ times i by dsimp [times]; linarith) tendsto_natCast_atTop_atTop
  have hnecks := hterminal
    (fun _ => FlowCarrier.ofConnectedManifold 3 (ULift.{u} L.convergence.limit.carrier.carrier))
    (fun i => Iio (-t₀ * Q i)) H (fun i => ULift.up (q i)) times R htimes hRt
    (fun _ => isOpen_Iio) (fun i => hwindow i (-times i))
    (fun i s hs => hcompleteH i s (interior_subset (hwindow i (-times i) hs)))
    (fun i s hs => hoperatorH i s (interior_subset (hwindow i (-times i) hs)))
    (fun i s hs => hscalarH i s hs.2) hnormalize
    (fun i s hs => hbaseH i s hs.2) hδ hδη.le G (hcomplete 0 hδ)
    Φ x hx hnormalized
  have hlarge : ∀ᶠ i in atTop, (ρ⁻¹) ^ 2 < Q (G.subsequence i) :=
    (hQt.comp G.subsequence_strictMono.tendsto_atTop).eventually
      (eventually_gt_atTop ((ρ⁻¹) ^ 2))
  obtain ⟨i, ⟨N, heps, hscale, _⟩, hi⟩ := (hnecks.and hlarge).exists
  have hmetric : ((H (G.subsequence i)).metric 0) =
      rescaledMetric (V.metric t₀) (Q (G.subsequence i)) (hQ (G.subsequence i)) := by
    simp only [H, RicciFlow.openAncientRescaleAt, RicciFlow.parabolicRescale_metric,
      zero_div, add_zero]
  obtain ⟨N₀, heps₀, hscale₀, _⟩ := EpsilonNeck.exists_of_metric_eq hmetric N
  obtain ⟨N', heps', hscale', _⟩ := EpsilonNeck.exists_of_rescaledMetric
    (Q (G.subsequence i)) (hQ (G.subsequence i)) N₀
  refine ⟨N', heps'.trans (heps₀.trans heps), ?_⟩
  rw [hscale', hscale₀, hscale]
  have hsqrt : ρ⁻¹ < Real.sqrt (Q (G.subsequence i)) :=
    (Real.lt_sqrt (inv_nonneg.mpr hρ.le)).mpr hi
  exact (div_lt_iff₀ (Real.sqrt_pos.mpr (hQ (G.subsequence i)))).mpr
    (by have := mul_lt_mul_of_pos_left hsqrt hρ; simpa only [mul_inv_cancel₀ hρ.ne'] using this)

theorem exists_small_neck_of_unbounded_scalarCurvature
    (P : ThreeDimensionalClassificationPredecessors.{u})
    (L : AncientAsymptoticSolitonLimitData S)
    {t₀ : ℝ} (ht₀ : t₀ < 0)
    (hunbounded : ¬ BddAbove
      (range (L.convergence.limit.flow.connection t₀).scalarCurvature))
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N : EpsilonNeck
        ((L.convergence.limit.flow.ulift :
          RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0)).metric t₀),
      N.epsilon = ε ∧ N.scale < ρ := by
  have hnoncompact : ¬ CompactSpace L.convergence.limit.carrier.carrier := by
    intro hcompact
    let := hcompact
    apply hunbounded
    simpa only [image_univ] using isCompact_univ.bddAbove_image
      (L.convergence.limit.continuous_scalarCurvature P.curvature t₀).continuousOn
  let : NoncompactSpace L.convergence.limit.carrier.carrier :=
    not_compactSpace_iff.mp hnoncompact
  have hpos := L.strictlyPositiveSectionalCurvature_of_unbounded_scalarCurvature
    P.curvature t₀ ht₀ hunbounded
  let g := L.convergence.limit.flow.metric t₀
  obtain ⟨p, o, c, hlevel, _⟩ :=
    g.exists_singleton_horoball_of_strictlyPositiveSectionalCurvature
      (L.convergence.limit.flow.connection t₀) (L.convergence.limit.complete t₀ ht₀) hpos
  obtain ⟨e, _⟩ := g.exists_euclidean_diffeomorph_of_singleton_horoball
      (L.convergence.limit.flow.connection t₀) (L.convergence.limit.complete t₀ ht₀)
      (hpos.nonnegative _) hlevel
  exact L.exists_small_neck_of_unbounded_scalarCurvature_of_euclidean P e.symm
    ht₀ hunbounded hε hεhalf hρ

end PoincareConjecture.AncientAsymptoticSolitonLimitData
