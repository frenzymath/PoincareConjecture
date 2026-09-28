import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Embeddings
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.JetSlices

set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

namespace AncientCompactness

theorem iteratedFDeriv_spatial_slice_of_open_halfspace
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) (f : ℝ × E → F)
    (hf : ContDiffOn ℝ ∞ f (Iic 0 ×ˢ U))
    {t : ℝ} (ht : t ≤ 0) {x : E} (hx : x ∈ U) (r : ℕ) :
    iteratedFDeriv ℝ r (fun y => f (t, y)) x =
      (iteratedFDerivWithin ℝ r f (Iic 0 ×ˢ (univ : Set E)) (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let ρ := δ / 2
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hball : closedBall x ρ ⊆ U :=
    (closedBall_subset_ball (by dsimp only [ρ]; linarith)).trans hδU
  have hset : Iic 0 ×ˢ closedBall x ρ =ᶠ[𝓝 (t, x)]
      Iic 0 ×ˢ (univ : Set E) := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds
      (isOpen_ball.mem_nhds (mem_ball_self hρ))] with z hz
    apply propext
    change (z.1 ≤ 0 ∧ z.2 ∈ closedBall x ρ) ↔ (z.1 ≤ 0 ∧ True)
    simp only [ball_subset_closedBall hz, and_true]
  rw [iteratedFDeriv_spatial_slice_of_centered_halfCylinder hρ f
    (hf.mono (prod_mono subset_rfl hball)) ht (mem_ball_self hρ) r,
    iteratedFDerivWithin_congr_set hset r]

end AncientCompactness

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalSpatialJetCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem tendstoUniformlyOn_spatialJets
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
        ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2)
    (q : G.limit.carrier.carrier) (j r : ℕ) (a b : Fin 3)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKU : K ⊆ {p | p.1 ≤ 0 ∧ p.2 ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p.2 ∈ G.exhaustion j}) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ r
        (fun y => normalizedKappaPullbackCoefficient (e k) q a b (p.1, y)) p.2)
      (fun p => iteratedFDeriv ℝ r
        (fun y => FlowCarrier.coordinateCoefficient G.limit.carrier q
          (fun t x v w => (G.limit.flow.flow.metric t).inner x v w) a b (p.1, y)) p.2)
      atTop K := by
  let f := fun k => normalizedKappaPullbackCoefficient (e k) q a b
  let g := FlowCarrier.coordinateCoefficient G.limit.carrier q
    (fun t x v w => (G.limit.flow.flow.metric t).inner x v w) a b
  have hraw : TendstoUniformlyOn (fun k => M23TerminalMetricJet r (f k))
      (M23TerminalMetricJet r g) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, _, hN⟩ := hconv q j r K hK hKU ε hε
    filter_upwards [eventually_ge_atTop N] with k hk p hp
    simpa only [dist_eq_norm, norm_sub_rev] using hN k hk a b p hp
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ)
    (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
  have hproject := P.uniformContinuous.comp_tendstoUniformlyOn hraw
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  apply (hproject.congr ?_).congr_right ?_
  · filter_upwards [eventually_ge_atTop j] with k hjk p hp
    let U := (extChartAt (𝓡 3) q).target ∩
      (extChartAt (𝓡 3) q).symm ⁻¹' G.exhaustion k
    have hU : IsOpen U :=
      (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
        (isOpen_extChartAt_target q) (G.exhaustion_open k)
    have hf : ContDiffOn ℝ ∞ (f k) (Iic 0 ×ˢ U) :=
      (e k).contDiffOn_terminalCoefficient (G.exhaustion_open k)
        (fun s t x hx hs ht => hfixed k s t x hs ht hx) q a b
    exact (AncientCompactness.iteratedFDeriv_spatial_slice_of_open_halfspace hU
      (f k) hf (hKU hp).1 ⟨(hKU hp).2.1, hmono hjk (hKU hp).2.2⟩ r).symm
  · intro p hp
    have hg : ContDiffOn ℝ ∞ g (Iic 0 ×ˢ (extChartAt (𝓡 3) q).target) :=
      (G.limit.flow.flow.contDiffOn_pullbackCoefficients_within
        (isOpen_extChartAt_target q) (contMDiffOn_extChartAt_symm (n := ∞) q))
        |>.clm_apply (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))
        |>.clm_apply (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
    exact (AncientCompactness.iteratedFDeriv_spatial_slice_of_open_halfspace
      (isOpen_extChartAt_target q) g hg (hKU hp).1 (hKU hp).2.1 r).symm

theorem tendstoUniformlyOn_fixedPullbackSpatialJets
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
        ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2)
    (q : G.limit.carrier.carrier) (j r : ℕ) (a b : Fin 3)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKU : K ⊆ {p | p.1 ≤ 0 ∧ p.2 ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p.2 ∈ G.exhaustion j}) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ r (fun y =>
        ((S.term (G.subsequence k)).flow.flow.metric p.1).pullbackCoefficients
          ((fun x => ((e k).toFun (0, x)).2) ∘ (extChartAt (𝓡 3) q).symm) y
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) p.2)
      (fun p => iteratedFDeriv ℝ r (fun y =>
        (G.limit.flow.flow.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm y
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) p.2)
      atTop K := by
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  apply (hconv.tendstoUniformlyOn_spatialJets hfixed q j r a b hK hKU).congr
  filter_upwards [eventually_ge_atTop j] with k hjk p hp
  let U := (extChartAt (𝓡 3) q).target ∩
    (extChartAt (𝓡 3) q).symm ⁻¹' G.exhaustion k
  have hU : IsOpen U :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion_open k)
  have hpU : p.2 ∈ U := ⟨(hKU hp).2.1, hmono hjk (hKU hp).2.2⟩
  have heq : (fun y => normalizedKappaPullbackCoefficient (e k) q a b (p.1, y))
      =ᶠ[𝓝 p.2] (fun y =>
        ((S.term (G.subsequence k)).flow.flow.metric p.1).pullbackCoefficients
          ((fun x => ((e k).toFun (0, x)).2) ∘ (extChartAt (𝓡 3) q).symm) y
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) := by
    filter_upwards [hU.mem_nhds hpU] with y hy
    exact (e k).terminal_coefficient_eq_fixed_pullback (G.exhaustion_open k)
      (fun s t x hx hs ht => hfixed k s t x hs ht hx) q a b
      (hKU hp).1 hy.1 hy.2
  exact (heq.iteratedFDeriv ℝ r).eq_of_nhds

end M23TerminalMetricConvergence

end PoincareConjecture
