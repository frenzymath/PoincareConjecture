import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Inheritance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.TerminalDerivatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.SpatialBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.CompactEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.CompactBallTransfer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

open SpacetimeBounds SpacetimeBounds.Bootstrap

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance embeddingBoundsCarrierConnected (C : FlowCarrier.{0} 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)

private theorem referenceChart_isLocalDiffeomorphAt
    (q : G.limitCarrier.carrier) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (extChartAt (𝓡 3) q).target) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (extChartAt (𝓡 3) q).symm x := by
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) G.limitCarrier.carrier
      (EuclideanSpace ℝ (Fin 3)) ∞ :=
    { toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin 3)) q).toPartialEquiv
      open_source := (chartAt (EuclideanSpace ℝ (Fin 3)) q).open_source
      open_target := (chartAt (EuclideanSpace ℝ (Fin 3)) q).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hxd : x ∈ d.symm.source := by
    change x ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q).target
    simpa only [extChartAt_target, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ] using hx
  exact d.symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hxd

theorem exists_pos_eventually_embedding_image_subset_terminalBall
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ k : ℕ in atTop,
      G.embedding k '' K ⊆
        ((S.term (G.subsequence k)).flow.flow.metric 0).ball
          (S.term (G.subsequence k)).base R := by
  let F (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  have hsub (k : ℕ) : Ioo (-1 : ℝ) 1 ⊆
      (fun t : ℝ => t - 1) ⁻¹' Iic 0 := by
    intro t ht
    change t - 1 ≤ 0
    linarith [ht.2]
  let W := G.window F (by norm_num : (-1 : ℝ) < 1) le_rfl 0 hsub
  obtain ⟨R, hR, hbound⟩ := W.exists_pos_eventually_image_subset_ballAt
    (by norm_num) (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1) hcomplete hK
  refine ⟨R, hR, ?_⟩
  filter_upwards [hbound] with k hk x hx
  have hx' : x ∈ ((S.term (G.subsequence k)).flow.flow.metric (0 - 1)).ball
      (S.term (G.subsequence k)).base R := by
    exact hk hx
  exact P.ball_monotone (S.term (G.subsequence k)).carrier.carrier
    (S.term (G.subsequence k)).flow (0 - 1) 0 (by norm_num) le_rfl
    (S.term (G.subsequence k)).base R hx'

theorem exists_pos_eventually_embedding_curvatureDerivativeNorm_le
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, t ≤ 0 → ∀ x ∈ K,
      ((S.term (G.subsequence k)).flow.flow.connection t).curvatureDerivativeNorm
        m (G.embedding k x) ≤ D := by
  obtain ⟨R, hR, himage⟩ :=
    S.exists_pos_eventually_embedding_image_subset_terminalBall G P hcomplete hK
  obtain ⟨D, hD, hbound⟩ := S.allTime_curvatureDerivativeNorm_le P hcontrol R hR m
  exact ⟨D, hD, himage.mono fun k hk t ht x hx =>
    hbound (G.subsequence k) t ht _ (hk (mem_image_of_mem _ hx))⟩

theorem eventually_embedding_chart_isLocalDiffeomorphAt
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ K,
      IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x := by
  have hc : ContinuousOn (extChartAt (𝓡 3) q).symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  have hmono : Monotone G.exhaustion :=
    monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j] with k hk x hx
  have he := G.embedding_smooth k
    ⟨(extChartAt (𝓡 3) q).symm x, hmono hk (hj (mem_image_of_mem _ hx))⟩
  exact (S.referenceChart_isLocalDiffeomorphAt G q (hKc hx)).comp
    (𝓡 3) (S.term (G.subsequence k)).carrier.carrier he

theorem embedding_coordinateCoefficient_eq_pullbackCoefficients
    (q : G.limitCarrier.carrier) (k : ℕ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (extChartAt (𝓡 3) q).target)
    (hxe : (extChartAt (𝓡 3) q).symm x ∈ G.exhaustion k) (a b : Fin 3) :
    G.limitCarrier.coordinateCoefficient q
      (fun s y v w => spatialPullbackInner G.limitCarrier
        (S.term (G.subsequence k)).carrier
        ((S.term (G.subsequence k)).flow.flow.metric (s - 1)) (G.embedding k) y v w)
      a b (t, x) =
    ((S.term (G.subsequence k)).flow.flow.metric (t - 1)).pullbackCoefficients
      (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) := by
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx).contMDiffAt
    (extChartAt_target_mem_nhds' hx)
  have he := (G.embedding_smooth k ⟨_, hxe⟩).contMDiffAt
  have hd : mfderiv (𝓡 3) (𝓡 3) (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x =
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) ((extChartAt (𝓡 3) q).symm x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm x) :=
    mfderiv_comp x (he.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  change ((S.term (G.subsequence k)).flow.flow.metric (t - 1)).inner
      (G.embedding k ((extChartAt (𝓡 3) q).symm x))
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) ((extChartAt (𝓡 3) q).symm x)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm x
          (EuclideanSpace.basisFun (Fin 3) ℝ a)))
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) ((extChartAt (𝓡 3) q).symm x)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm x
          (EuclideanSpace.basisFun (Fin 3) ℝ b))) = _
  unfold RiemannianMetric.pullbackCoefficients
  erw [hd]
  rfl

theorem tendstoUniformlyOn_embedding_coordinate_metricJet
    (q : G.limitCarrier.carrier) (r : ℕ) (a b : Fin 3)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKt : ∀ z ∈ K, z.1 < 1)
    (hKc : ∀ z ∈ K, z.2 ∈ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w => spatialPullbackInner G.limitCarrier
          (S.term (G.subsequence k)).carrier
          ((S.term (G.subsequence k)).flow.flow.metric (t - 1))
          (G.embedding k) x v w) a b))
      (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metric t) x v w) a b))
      atTop K := by
  let f := fun z : ℝ × EuclideanSpace ℝ (Fin 3) => (extChartAt (𝓡 3) q).symm z.2
  have hf : ContinuousOn f K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.comp
      continuous_snd.continuousOn hKc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hf)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j r K hK
    (fun z hz => ⟨hKt z hz, hKc z hz, hj (mem_image_of_mem f hz)⟩) ε hε
  exact (eventually_ge_atTop N).mono fun k hk z hz => by
    simpa only [dist_eq_norm, norm_sub_rev, MetricJet] using hN k hk a b z hz

noncomputable def coefficientEval (a b : Fin 3) :
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b)).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
      (EuclideanSpace.basisFun (Fin 3) ℝ a))

theorem exists_bilinear_jet_norm_le_components
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (Q : X [×m]→L[ℝ]
          (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ))
        (B : ℝ), 0 ≤ B →
        (∀ a b, ‖(coefficientEval a b).compContinuousMultilinearMap Q‖ ≤ B) →
        ‖Q‖ ≤ D * B := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  obtain ⟨D₁, hD₁, h₁⟩ := b.exists_opNorm_le
    (F := EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
  obtain ⟨D₂, hD₂, h₂⟩ := b.exists_opNorm_le (F := ℝ)
  refine ⟨D₁ * D₂, mul_pos hD₁ hD₂, fun Q B hB hcoeff => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hc (a c : Fin 3) : ‖Q v (b a) (b c)‖ ≤ B * ∏ i, ‖v i‖ :=
    ((coefficientEval a c).compContinuousMultilinearMap Q).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right (hcoeff a c) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  have hinner (a : Fin 3) : ‖Q v (b a)‖ ≤ D₂ * (B * ∏ i, ‖v i‖) :=
    h₂ (by positivity) (hc a)
  simpa only [mul_assoc] using h₁ (by positivity) hinner

theorem exists_eventually_embedding_reference_metric_jet_bound
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m
        (((S.term (G.subsequence k)).flow.flow.metric (-1)).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm)) x‖ ≤ B := by
  let F (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  have hsub (k : ℕ) : Ioo (-1 : ℝ) 1 ⊆
      (fun t : ℝ => t - 1) ⁻¹' Iic 0 := by
    intro t ht
    change t - 1 ≤ 0
    linarith [ht.2]
  let W := G.window F (by norm_num : (-1 : ℝ) < 1) le_rfl 0 hsub
  let f := fun k a b (x : EuclideanSpace ℝ (Fin 3)) =>
    G.limitCarrier.coordinateCoefficient q
      (fun s y v w => spatialPullbackInner G.limitCarrier
        (S.term (G.subsequence k)).carrier
        ((S.term (G.subsequence k)).flow.flow.metric (s - 1)) (G.embedding k) y v w)
      a b (0, x)
  let g := fun a b (x : EuclideanSpace ℝ (Fin 3)) =>
    G.limitCarrier.coordinateCoefficient q
      (fun s y v w => G.limitCarrier.metricInner (G.limitFlow.metric s) y v w) a b (0, x)
  have hconv (a b : Fin 3) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k a b)) (iteratedFDeriv ℝ m (g a b)) atTop K := by
    exact W.tendstoUniformlyOn_coordinate_spatial_metricJet q m a b 0
      (by norm_num) K hK hKc
  have hdiff (a b : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ K) :
      ContDiffAt ℝ ∞ (g a b) x := by
    exact (W.limitFlow.contDiffAt_coordinateCoefficient_metric q a b (0, x)
      (by norm_num) (hKc hx)).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hcomponent (a b : Fin 3) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f k a b) x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      (fun x hx => ((hdiff a b x hx).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)).continuousWithinAt)
    refine ⟨max (B + 1) 0, le_max_right _ _, ?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv a b) 1 zero_lt_one]
      with k hk x hx
    apply le_trans _ (le_max_left (B + 1) 0)
    exact (norm_le_norm_add_norm_sub (iteratedFDeriv ℝ m (g a b) x)
      (iteratedFDeriv ℝ m (f k a b) x)).trans
        (add_le_add (hB x hx) (by
          have hdist := (hk x hx).le
          rw [dist_eq_norm] at hdist
          exact hdist))
  choose B hB hbound using hcomponent
  let C := ∑ a : Fin 3, ∑ b : Fin 3, B a b
  have hC : 0 ≤ C := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hB a b
  have hBC (a b : Fin 3) : B a b ≤ C := by
    apply (Finset.single_le_sum (fun b _ => hB a b) (Finset.mem_univ b)).trans
    exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => hB a b)
      (Finset.mem_univ a)
  obtain ⟨D, hD, hnorm⟩ := exists_bilinear_jet_norm_le_components
    (EuclideanSpace ℝ (Fin 3)) m
  have hc : ContinuousOn (extChartAt (𝓡 3) q).symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  refine ⟨D * C, mul_nonneg hD.le hC, ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (hbound a)),
    eventually_ge_atTop j, S.eventually_embedding_chart_isLocalDiffeomorphAt G q hK hKc]
    with k hk hjk hs x hx
  let A := ((S.term (G.subsequence k)).flow.flow.metric (-1)).pullbackCoefficients
    (G.embedding k ∘ (extChartAt (𝓡 3) q).symm)
  have hA : ContDiffAt ℝ ∞ A x :=
    ((S.term (G.subsequence k)).flow.flow.metric (-1)).contDiffAt_pullbackCoefficients
      (hs x hx).contMDiffAt
  apply hnorm _ C hC
  intro a b
  have heq : f k a b =ᶠ[𝓝 x] (coefficientEval a b ∘ A) := by
    have hcx := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q (hKc hx)).contMDiffAt
      (extChartAt_target_mem_nhds' (hKc hx))
    filter_upwards [extChartAt_target_mem_nhds' (hKc hx),
      hcx.continuousAt.preimage_mem_nhds
        ((G.exhaustion_open k).mem_nhds (hmono hjk (hj (mem_image_of_mem _ hx))))]
      with y hy hye
    have h := S.embedding_coordinateCoefficient_eq_pullbackCoefficients G q k 0 y hy hye a b
    simp only [zero_sub] at h
    convert! h using 1
  have hderiv := (heq.iteratedFDeriv ℝ m).self_of_nhds
  rw [(coefficientEval a b).iteratedFDeriv_comp_left hA
    (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)] at hderiv
  exact (hderiv ▸ hk a b x hx).trans (hBC a b)

theorem exists_eventually_embedding_reference_ellipticity
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ∀ v,
      a * ‖v‖ ^ 2 ≤ ((S.term (G.subsequence k)).flow.flow.metric (-1)).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x v v ∧
      ((S.term (G.subsequence k)).flow.flow.metric (-1)).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x v v ≤ b * ‖v‖ ^ 2 := by
  let c := extChartAt (𝓡 3) q
  let B := (G.limitFlow.metric 0).pullbackCoefficients c.symm
  have hB : ContinuousOn B K := fun x hx =>
    ((G.limitFlow.metric 0).contDiffAt_pullbackCoefficients
      (S.referenceChart_isLocalDiffeomorphAt G q (hKc hx)).contMDiffAt).continuousAt.continuousWithinAt
  have hpos : ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 → 0 < B x v v := by
    intro x hx v hv
    apply (G.limitFlow.metric 0).pos
    have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm x).IsInvertible :=
      ⟨(S.referenceChart_isLocalDiffeomorphAt G q (hKc hx)).mfderivToContinuousLinearEquiv
        (by simp), rfl⟩
    intro hz
    apply hv
    apply hi.injective
    rw [map_zero]
    convert! hz using 1
  obtain ⟨α, hα, hlower⟩ := exists_uniform_bilinear_family_lower_bound hK hB hpos
  obtain ⟨β, hβ⟩ := hK.exists_bound_of_continuousOn hB
  let F (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  have hsub (k : ℕ) : Ioo (-1 : ℝ) 1 ⊆
      (fun t : ℝ => t - 1) ⁻¹' Iic 0 := by
    intro t ht
    change t - 1 ≤ 0
    linarith [ht.2]
  let W := G.window F (by norm_num : (-1 : ℝ) < 1) le_rfl 0 hsub
  have hc : ContinuousOn c.symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  have himage := hK.image_of_continuousOn hc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset himage
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  refine ⟨α / 2, 2 * max β 1, by positivity, mul_pos (by norm_num) (lt_max_of_lt_right zero_lt_one), ?_⟩
  filter_upwards [W.eventually_pullback_inner_bounds himage
      (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1) (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop j] with k hk hjk x hx v
  let w := mfderiv (𝓡 3) (𝓡 3) c.symm x v
  have hcomparison := hk (c.symm x) (mem_image_of_mem _ hx) w
  have he := (G.embedding_smooth k ⟨_, hmono hjk (hj (mem_image_of_mem _ hx))⟩).contMDiffAt
  have hd : mfderiv (𝓡 3) (𝓡 3) (G.embedding k ∘ c.symm) x =
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) (c.symm x)).comp
        (mfderiv (𝓡 3) (𝓡 3) c.symm x) :=
    mfderiv_comp x (he.mdifferentiableAt (by simp))
      ((S.referenceChart_isLocalDiffeomorphAt G q (hKc hx)).contMDiffAt.mdifferentiableAt (by simp))
  have heq : pullbackInnerValue W.limitFlow _ (W.embedding k) 0 (c.symm x) w w =
      ((S.term (G.subsequence k)).flow.flow.metric (-1)).pullbackCoefficients
        (G.embedding k ∘ c.symm) x v v := by
    change ((S.term (G.subsequence k)).flow.flow.metric (0 - 1)).inner
      (G.embedding k (c.symm x))
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) (c.symm x) w)
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) (c.symm x) w) = _
    unfold RiemannianMetric.pullbackCoefficients
    erw [hd]
    rw [zero_sub]
    rfl
  have href : W.limitCarrier.metricInner (W.limitFlow.metricAt 0) (c.symm x) w w = B x v v := rfl
  rw [heq, href] at hcomparison
  have hupper : B x v v ≤ max β 1 * ‖v‖ ^ 2 := by
    apply (le_abs_self _).trans
    calc
      |B x v v| ≤ ‖B x‖ * (‖v‖ * ‖v‖) := by
        simpa only [Real.norm_eq_abs, mul_assoc] using (B x).le_opNorm₂ v v
      _ ≤ max β 1 * ‖v‖ ^ 2 := by
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_right (hβ x hx |>.trans (le_max_left β 1))
            (mul_nonneg (norm_nonneg v) (norm_nonneg v))
  have hnonneg : 0 ≤ B x v v := le_trans (by positivity) (hlower x hx v)
  constructor
  · nlinarith [hlower x hx v]
  · nlinarith

theorem exists_eventually_embedding_closed_ellipticity
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    {d : ℝ} (hd : 1 ≤ d) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Icc (-d) 0, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((S.term (G.subsequence k)).flow.flow.metric t).pullbackCoefficients
            (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x v v ∧
        ((S.term (G.subsequence k)).flow.flow.metric t).pullbackCoefficients
            (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x v v ≤ b * ‖v‖ ^ 2 := by
  have hc : ContinuousOn (extChartAt (𝓡 3) q).symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨R, hR, himage⟩ := S.exists_pos_eventually_embedding_image_subset_terminalBall
    G P hcomplete (hK.image_of_continuousOn hc)
  obtain ⟨C, hC, hcurv⟩ := hcontrol R hR
  obtain ⟨α, β, hα, hβ, href⟩ :=
    S.exists_eventually_embedding_reference_ellipticity G q hK hKc
  let D : ℝ := (3 : ℝ) ^ 3 * C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨Real.exp (-(2 * D) * d) * α, Real.exp (2 * D * d) * β,
    mul_pos (Real.exp_pos _) hα, mul_pos (Real.exp_pos _) hβ, ?_⟩
  filter_upwards [himage, href] with k hk hreference t ht x hx v
  let F := (S.term (G.subsequence k)).flow.flow
  let e := G.embedding k ∘ (extChartAt (𝓡 3) q).symm
  let w := mfderiv (𝓡 3) (𝓡 3) e x v
  have hxball : e x ∈ (F.metric 0).ball (S.term (G.subsequence k)).base R :=
    hk (mem_image_of_mem _ (mem_image_of_mem _ hx))
  have hnonneg (u : ℝ) : 0 ≤ (F.metric u).inner (e x) w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact ((F.metric u).pos _ _ hw).le
  have hRic : ∀ u ∈ Icc (-d) 0,
      |(F.connection u).ricci (e x) w w| ≤ D * (F.metric u).inner (e x) w w := by
    intro u hu
    have h := (F.connection u).abs_ricci_quadratic_le_curvatureTensorNorm (e x) w
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) (e x)) = 3 := finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hcurv (G.subsequence k) u hu.2 _ hxball))
        (by positivity)) (hnonneg u))
  have hcomp := F.metric_inner_self_exp_bounds (convex_Icc (-d) 0)
    (fun _ hu => hu.2) (e x) w D hRic
    (show (-1 : ℝ) ∈ Icc (-d) 0 by constructor <;> linarith) ht
  have hdist : |t - (-1)| ≤ d := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hreference := hreference x hx v
  change α * ‖v‖ ^ 2 ≤ (F.metric (-1)).inner (e x) w w ∧
    (F.metric (-1)).inner (e x) w w ≤ β * ‖v‖ ^ 2 at hreference
  constructor
  · calc
      (Real.exp (-(2 * D) * d) * α) * ‖v‖ ^ 2 =
          Real.exp (-(2 * D) * d) * (α * ‖v‖ ^ 2) := mul_assoc _ _ _
      _ ≤ Real.exp (-(2 * D) * d) * (F.metric (-1)).inner (e x) w w :=
        mul_le_mul_of_nonneg_left hreference.1 (Real.exp_nonneg _)
      _ ≤ Real.exp (-(2 * D) * |t - (-1)|) * (F.metric (-1)).inner (e x) w w :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hdist (by linarith))) (hnonneg (-1))
      _ ≤ _ := hcomp.1
  · calc
      _ ≤ Real.exp (2 * D * |t - (-1)|) * (F.metric (-1)).inner (e x) w w := hcomp.2
      _ ≤ Real.exp (2 * D * d) * (F.metric (-1)).inner (e x) w w :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hdist (by positivity))) (hnonneg (-1))
      _ ≤ Real.exp (2 * D * d) * (β * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hreference.2 (Real.exp_nonneg _)
      _ = (Real.exp (2 * D * d) * β) * ‖v‖ ^ 2 := (mul_assoc _ _ _).symm

theorem exists_eventually_embedding_closed_spatial_jet_bound
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    {d : ℝ} (hd : 1 ≤ d) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Icc (-d) 0, ∀ x ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j
          (((S.term (G.subsequence k)).flow.flow.metric t).pullbackCoefficients
            (G.embedding k ∘ (extChartAt (𝓡 3) q).symm)) x‖ ≤ B := by
  obtain ⟨α, β, hα, hβ, hell⟩ :=
    S.exists_eventually_embedding_closed_ellipticity G P hcontrol hcomplete q hK hKc hd
  have hc : ContinuousOn (extChartAt (𝓡 3) q).symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  have himage := hK.image_of_continuousOn hc
  obtain ⟨j₀, hj₀⟩ := G.exists_exhaustion_superset himage
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  induction m with
  | zero =>
      refine ⟨β, hβ.le, hell.mono ?_⟩
      intro k hk t ht x hx j hj
      have hj0 : j = 0 := by omega
      subst j
      rw [norm_iteratedFDeriv_zero]
      apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hβ.le
      · exact fun v w => ((S.term (G.subsequence k)).flow.flow.metric t).symm _ _ _
      · intro v
        rw [abs_of_nonneg (le_trans (by positivity) (hk t ht x hx v).1)]
        exact (hk t ht x hx v).2
  | succ l ih =>
      obtain ⟨B, hB, hprevious⟩ := ih
      let A : ℝ := max B 1
      have hA : 1 ≤ A := le_max_right _ _
      choose D hD hcurv using fun j =>
        S.exists_pos_eventually_embedding_curvatureDerivativeNorm_le G P hcontrol hcomplete himage j
      obtain ⟨C, hC, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
        3 l D (fun j => (hD j).le) hα hβ.le A hA
      obtain ⟨Z, _, hinit⟩ := S.exists_eventually_embedding_reference_metric_jet_bound G q hK hKc (l + 1)
      let E : ℝ := max Z 1 * Real.exp ((C + C) * d)
      have hE : 0 ≤ E := by dsimp [E]; positivity
      refine ⟨max B E, le_max_of_le_left hB, ?_⟩
      filter_upwards [hprevious, hinit, hell, eventually_ge_atTop j₀,
        (eventually_all_finite (Set.finite_Iic (l + 1))).mpr (fun j _ => hcurv j)]
        with k hprev href hellk hstage hcurvk t ht x hx j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · apply le_trans _ (le_max_right B E)
        let F := (S.term (G.subsequence k)).flow.flow
        let c := extChartAt (𝓡 3) q
        let e := G.embedding k ∘ c.symm
        let U := c.target ∩ c.symm ⁻¹' G.exhaustion k
        have hU : IsOpen U := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
          (isOpen_extChartAt_target q) (G.exhaustion_open k)
        have hKsub : K ⊆ U := fun y hy =>
          ⟨hKc hy, hmono hstage (hj₀ (mem_image_of_mem _ hy))⟩
        have heDiff (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
            IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e y :=
          (S.referenceChart_isLocalDiffeomorphAt G q hy.1).comp
            (𝓡 3) (S.term (G.subsequence k)).carrier.carrier (G.embedding_smooth k ⟨_, hy.2⟩)
        have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U :=
          fun y hy => (heDiff y hy).contMDiffAt.contMDiffWithinAt
        have hi : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible :=
          fun y hy => ⟨(heDiff y hy).mfderivToContinuousLinearEquiv (by simp), rfl⟩
        let Fneg := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
          (show Iio (0 : ℝ) ⊆ Iic 0 from fun s hs => show s ≤ 0 from le_of_lt hs)
          ordConnected_Iio (show (Iio (0 : ℝ)).Nontrivial from
            ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩)
        have hjoint : ContDiffOn ℝ ∞
            (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
              iteratedFDeriv ℝ (l + 1) ((F.metric z.1).pullbackCoefficients e) z.2)
            (Iic 0 ×ˢ U) := contDiffOn_spatialJet_within
          (F.contDiffOn_pullbackCoefficients_within hU he) (uniqueDiffOn_Iic 0) hU (l + 1)
        have hcont : ContinuousOn
            (fun s => iteratedFDeriv ℝ (l + 1) ((F.metric s).pullbackCoefficients e) x)
            (Icc (-d) 0) := by
          have htime : Continuous (fun u : ℝ => (u, x)) :=
            continuous_id.prodMk continuous_const
          exact hjoint.continuousOn.comp (f := fun u : ℝ => (u, x)) htime.continuousOn
            (show MapsTo (fun u : ℝ => (u, x)) (Icc (-d) 0) (Iic 0 ×ˢ U) from
              fun _ hs => ⟨hs.2, hKsub hx⟩)
        have hdiff : ∀ s ∈ Ioo (-d) 0, DifferentiableAt ℝ
            (fun u => iteratedFDeriv ℝ (l + 1) ((F.metric u).pullbackCoefficients e) x) s := by
          intro s hs
          have hsm := SpacetimeBounds.contDiffOn_spatialJet
            (Fneg.contDiffOn_pullbackCoefficients isOpen_Iio hU he) isOpen_Iio hU (l + 1)
          exact ((hsm.contDiffAt (x := (s, x))
            ((isOpen_Iio.prod hU).mem_nhds ⟨hs.2, hKsub hx⟩)).comp s
            (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
        have hbound : ∀ s ∈ Ioo (-d) 0,
            ‖deriv (fun u => iteratedFDeriv ℝ (l + 1)
              ((F.metric u).pullbackCoefficients e) x) s‖ ≤
              C + C * ‖iteratedFDeriv ℝ (l + 1) ((F.metric s).pullbackCoefficients e) x‖ := by
          intro s hs
          have hsclosed : s ∈ Icc (-d) 0 := ⟨hs.1.le, hs.2.le⟩
          have h := hevol Fneg isOpen_Iio hU he hi hs.2 (hKsub hx)
            (fun v => (hellk s hsclosed x hx v).1) (fun v => (hellk s hsclosed x hx v).2)
            (fun a ha => hcurvk a ha s hs.2.le _ (mem_image_of_mem _ hx))
            (fun a ha hal => (hprev s hsclosed x hx a hal).trans
              ((le_max_left B 1).trans (by simpa only [pow_one] using pow_le_pow_right₀ hA ha)))
          change ‖deriv (fun u => iteratedFDeriv ℝ (l + 1)
            ((F.metric u).pullbackCoefficients e) x) s‖ ≤
              C * (1 + ‖iteratedFDeriv ℝ (l + 1) ((F.metric s).pullbackCoefficients e) x‖) at h
          simpa only [mul_add, mul_one] using h
        have hprop := SpacetimeBounds.norm_le_exp_of_affine_deriv_bound_Icc_reference
          hcont hdiff hC hC (show (-1 : ℝ) ∈ Icc (-d) 0 by constructor <;> linarith)
          (href x hx) hbound ht
        apply hprop.trans
        apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) (le_max_right Z 1))
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (add_nonneg hC hC)
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      · exact (hprev t ht x hx j (by omega)).trans (le_max_left B E)

theorem exists_eventually_embedding_open_spacetime_jet_bound
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target)
    {d : ℝ} (hd : 1 ≤ d) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Ioo (-d) 0, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
          ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
            (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) z.2) (t, x)‖ ≤ B := by
  let E := EuclideanSpace ℝ (Fin 3)
  let c := extChartAt (𝓡 3) q
  let e := fun k => G.embedding k ∘ c.symm
  let U := fun k => c.target ∩ c.symm ⁻¹' G.exhaustion k
  have hU (k : ℕ) : IsOpen (U k) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion_open k)
  have heDiff (k : ℕ) (x : E) (hx : x ∈ U k) :
      IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (e k) x :=
    (S.referenceChart_isLocalDiffeomorphAt G q hx.1).comp
      (𝓡 3) (S.term (G.subsequence k)).carrier.carrier (G.embedding_smooth k ⟨_, hx.2⟩)
  have he (k : ℕ) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e k) (U k) :=
    fun x hx => (heDiff k x hx).contMDiffAt.contMDiffWithinAt
  have hi (k : ℕ) : ∀ x ∈ U k, (mfderiv (𝓡 3) (𝓡 3) (e k) x).IsInvertible :=
    fun x hx => ⟨(heDiff k x hx).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  let Fneg (k : ℕ) := Poincare.Geometry.RicciFlow.Harnack.restrictFlow
    (S.term (G.subsequence k)).flow.flow
    (show Iio (0 : ℝ) ⊆ Iic 0 from fun t ht => show t ≤ 0 from le_of_lt ht)
    ordConnected_Iio (show (Iio (0 : ℝ)).Nontrivial from
      ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩)
  let f := fun k (z : ℝ × E) =>
    ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients (e k) z.2
  let W := fun k => Ioo (-d) 0 ×ˢ (K ∩ U k)
  have hf (k : ℕ) : ContDiffOn ℝ ∞ (f k) (Iio 0 ×ˢ U k) :=
    (Fneg k).contDiffOn_pullbackCoefficients isOpen_Iio (hU k) (he k)
  have hrange (k : ℕ) : MapsTo (spatialJet 2 (f k)) (Iio 0 ×ˢ U k) (jetRicciFlowDomain 3) := by
    intro z hz
    change ((twoJetProjection 3 (spatialJet 2 (f k) z)).1).IsInvertible
    rw [twoJetProjection_spatialJet]
    exact ((S.term (G.subsequence k)).flow.flow.metric z.1).isInvertible_pullbackCoefficients
      (hi k z.2 hz.2).injective
  have hevol (k : ℕ) (z : ℝ × E) (hz : z ∈ Iio 0 ×ˢ U k) :
      deriv (fun t => f k (t, z.2)) z.1 = jetRicciFlowOperator 3 (spatialJet 2 (f k) z) := by
    rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
    exact deriv_pullbackCoefficients_eq_ricciFlowOperator (Fneg k)
      isOpen_Iio (hU k) (he k) (hi k) hz.1 hz.2
  have hall (r : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ W k, ∀ j ≤ r, ‖iteratedFDeriv ℝ j (fun x => f k (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hbound⟩ :=
      S.exists_eventually_embedding_closed_spatial_jet_bound G P hcontrol hcomplete q hK hKc hd r
    exact ⟨B, hB, hbound.mono fun k hk z hz j hj =>
      hk z.1 ⟨hz.1.1.le, hz.1.2.le⟩ z.2 hz.2.1 j hj⟩
  have hspatial (r : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ W k, ‖iteratedFDeriv ℝ r (fun x => f k (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hbound⟩ := hall r
    exact ⟨B, hB, hbound.mono fun k hk z hz => hk z hz r le_rfl⟩
  obtain ⟨a, b, ha, _, hell⟩ :=
    S.exists_eventually_embedding_closed_ellipticity G P hcontrol hcomplete q hK hKc hd
  have hcompact (r : ℕ) : ∃ Q : Set (Jet E (MetricCoefficient 3) (2 + r)),
      IsCompact Q ∧ Q ⊆ (baseProjection 2 r) ⁻¹' jetRicciFlowDomain 3 ∧
        ∀ᶠ k : ℕ in atTop, MapsTo (spatialJet (2 + r) (f k)) (W k) Q := by
    obtain ⟨B, hB, hbound⟩ := hall (2 + r)
    obtain ⟨Q, hQ, hQU, hbox⟩ := exists_compact_elliptic_jet_box 3 r ha B
    refine ⟨Q, hQ, hQU, ?_⟩
    filter_upwards [hbound, hell] with k hk heq z hz
    apply hbox
    · exact (pi_norm_le_iff_of_nonneg hB).mpr (fun j => hk z hz j (by omega))
    · intro v
      exact (heq z.1 ⟨hz.1.1.le, hz.1.2.le⟩ z.2 hz.2.1 v).1
  obtain ⟨B, hB, hbound⟩ := eventuallyBounded_spacetime_jets atTop
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3)
    f (fun _ => Iio 0) U W hf (fun _ => isOpen_Iio) hU
    (fun _ _ hz => ⟨hz.1.2, hz.2.2⟩) hrange hevol hspatial hcompact m
  have hc : ContinuousOn c.symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop j] with k hk hjk t ht x hx
  exact hk (t, x) ⟨ht, hx, hKc hx, hmono hjk (hj (mem_image_of_mem _ hx))⟩

theorem eventually_embedding_contDiffOn_terminal
    (q : G.limitCarrier.carrier) {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ}
    (hchart : Metric.closedBall x₀ ρ ⊆ (extChartAt (𝓡 3) q).target) :
    ∀ᶠ k : ℕ in atTop, ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
        ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) z.2)
      (Iic 0 ×ˢ Metric.closedBall x₀ ρ) := by
  let c := extChartAt (𝓡 3) q
  have hc : ContinuousOn c.symm (Metric.closedBall x₀ ρ) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hchart
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    ((isCompact_closedBall x₀ ρ).image_of_continuousOn hc)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j] with k hjk
  let U := c.target ∩ c.symm ⁻¹' G.exhaustion k
  have hU : IsOpen U := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_target q) (G.exhaustion_open k)
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (G.embedding k ∘ c.symm) U := by
    intro x hx
    exact ((S.referenceChart_isLocalDiffeomorphAt G q hx.1).comp
      (𝓡 3) (S.term (G.subsequence k)).carrier.carrier
      (G.embedding_smooth k ⟨_, hx.2⟩)).contMDiffAt.contMDiffWithinAt
  exact ((S.term (G.subsequence k)).flow.flow.contDiffOn_pullbackCoefficients_within hU he).mono
    (prod_mono subset_rfl fun x hx => ⟨hchart hx, hmono hjk (hj (mem_image_of_mem _ hx))⟩)

theorem exists_eventually_embedding_terminal_jet_bound
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ} (hρ : 0 < ρ)
    (hchart : Metric.closedBall x₀ ρ ⊆ (extChartAt (𝓡 3) q).target)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKΩ : K ⊆ Iic 0 ×ˢ Metric.closedBall x₀ ρ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
      ‖iteratedFDerivWithin ℝ m (fun w : ℝ × EuclideanSpace ℝ (Fin 3) =>
        ((S.term (G.subsequence k)).flow.flow.metric w.1).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) w.2)
        (Iic 0 ×ˢ Metric.closedBall x₀ ρ) z‖ ≤ B := by
  let E := EuclideanSpace ℝ (Fin 3)
  let Ω : Set (ℝ × E) := Iic 0 ×ˢ Metric.closedBall x₀ ρ
  have hconvex : Convex ℝ Ω := (convex_Iic 0).prod (convex_closedBall x₀ ρ)
  have hne : (interior Ω).Nonempty := by
    rw [show Ω = Iic 0 ×ˢ Metric.closedBall x₀ ρ from rfl,
      interior_prod_eq, interior_Iic, interior_closedBall x₀ hρ.ne']
    exact ⟨(-1, x₀), by simp [hρ]⟩
  have hunique := uniqueDiffOn_convex hconvex hne
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn
    (continuous_fst.continuousOn : ContinuousOn (fun z : ℝ × E => z.1) K)
  let d := max b 1 + 1
  have hd : 1 ≤ d := by dsimp [d]; linarith [le_max_right b 1]
  obtain ⟨B, hB, hbound⟩ := S.exists_eventually_embedding_open_spacetime_jet_bound
    G P hcontrol hcomplete q (isCompact_closedBall x₀ ρ) hchart hd m
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound, S.eventually_embedding_contDiffOn_terminal G q hchart]
    with k hk hf z hz
  let f : ℝ × E → MetricCoefficient 3 := fun w =>
    ((S.term (G.subsequence k)).flow.flow.metric w.1).pullbackCoefficients
      (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) w.2
  let U : Set (ℝ × E) := Ioo (-d) 0 ×ˢ Metric.ball x₀ ρ
  have hUo : IsOpen U := isOpen_Ioo.prod Metric.isOpen_ball
  have hUΩ : U ⊆ Ω := prod_mono (fun _ ht => ht.2.le) Metric.ball_subset_closedBall
  have hzclosure : z ∈ closure U := by
    rw [show U = Ioo (-d) 0 ×ˢ Metric.ball x₀ ρ from rfl, closure_prod_eq,
      closure_Ioo (by linarith : -d ≠ 0), closure_ball x₀ hρ.ne']
    refine ⟨⟨?_, (hKΩ hz).1⟩, (hKΩ hz).2⟩
    have hbz : -b ≤ z.1 := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hb z hz)).1
    dsimp [d]
    linarith [le_max_left b 1]
  have hm : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)
  apply ContinuousWithinAt.closure_le hzclosure
    ((hf.continuousOn_iteratedFDerivWithin hm hunique z (hKΩ hz)).norm.mono hUΩ)
    continuousWithinAt_const
  intro y hy
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hunique
    ((hf.contDiffAt (mem_of_superset (hUo.mem_nhds hy) hUΩ)).of_le hm) (hUΩ hy)]
  exact hk y.1 hy.1 y.2 (Metric.ball_subset_closedBall hy.2)

end PoincareConjecture.NormalizedKappaSolutionSequence
