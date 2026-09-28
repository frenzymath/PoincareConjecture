import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.TerminalConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.JetSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.PartialCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature.MovingJets











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1000000
set_option maxSynthPendingDepth 32
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalCurvatureCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)
  (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
  (hF : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1))
  (P : M23NormalizedKappaCompactnessPredecessors)
  (hcontrol : M23AllTimeCurvatureControl S)
  (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))

include hF P hcontrol hcomplete



theorem tendsto_terminal_spatial_pullbackJet
    (q : G.limitCarrier.carrier) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ (extChartAt (𝓡 3) q).target) {t : ℝ} (ht : t ≤ 0)
    (r : ℕ) (a b : Fin 3) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun x =>
      ((S.term (G.subsequence k)).flow.flow.metric t).pullbackCoefficients
        (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p)
      atTop (𝓝 (iteratedFDeriv ℝ r (fun x =>
        (F.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm x
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p)) := by
  let E := EuclideanSpace ℝ (Fin 3)
  let f := fun k (z : ℝ × E) =>
    ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
      (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) z.2
  let g := fun z : ℝ × E =>
    (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm z.2
  obtain ⟨ε, hε, hεc⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hp)
  let ρ := ε / 2
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hchart : Metric.closedBall p ρ ⊆ (extChartAt (𝓡 3) q).target :=
    (Metric.closedBall_subset_ball (by dsimp only [ρ]; linarith)).trans hεc
  have hpball : p ∈ Metric.ball p ρ := Metric.mem_ball_self hρ
  have hg : ContDiffOn ℝ ∞ g (Iic 0 ×ˢ Metric.closedBall p ρ) :=
    (F.contDiffOn_pullbackCoefficients_within (isOpen_extChartAt_target q)
      (contMDiffOn_extChartAt_symm (n := ∞) q)).mono (prod_mono subset_rfl hchart)
  have hf := S.eventually_embedding_contDiffOn_terminal G q hchart
  have hjet := S.tendstoUniformlyOn_terminal_bilinearJet_on_closedBall G F hF P
    hcontrol hcomplete q hρ hchart r (K := {(t, p)}) isCompact_singleton
    (singleton_subset_iff.mpr ⟨show t ∈ Iic 0 from ht, Metric.mem_closedBall_self hρ.le⟩)
  let R := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
  have hrestricted := R.continuous.continuousAt.tendsto.comp
    (hjet.tendsto_at (mem_singleton (t, p)))
  have hspatial : Tendsto (fun k => iteratedFDeriv ℝ r (fun x => f k (t, x)) p)
      atTop (𝓝 (iteratedFDeriv ℝ r (fun x => g (t, x)) p)) := by
    have htarget := AncientCompactness.iteratedFDeriv_spatial_slice_of_centered_halfCylinder
      hρ g hg ht hpball r
    change iteratedFDeriv ℝ r (fun x => g (t, x)) p =
      R (iteratedFDerivWithin ℝ r g (Iic 0 ×ˢ Metric.closedBall p ρ) (t, p)) at htarget
    rw [← htarget] at hrestricted
    apply hrestricted.congr'
    filter_upwards [hf] with k hk
    exact (AncientCompactness.iteratedFDeriv_spatial_slice_of_centered_halfCylinder
      hρ (f k) hk ht hpball r).symm
  have hsmoothg : ContDiffAt ℝ ∞ (fun x => g (t, x)) p := by
    have hslice : ContDiffOn ℝ ∞ (fun x => g (t, x)) (Metric.closedBall p ρ) :=
      hg.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => ⟨ht, hx⟩)
    exact hslice.contDiffAt
      (mem_of_superset (Metric.isOpen_ball.mem_nhds hpball) Metric.ball_subset_closedBall)
  have hr : (r : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (r : ℕ∞) ≤ ⊤)
  have hscalar := (coefficientEval a b).continuous_postcomp_continuousMultilinearMap
    |>.continuousAt.tendsto.comp hspatial
  rw [← (coefficientEval a b).iteratedFDeriv_comp_left hsmoothg hr] at hscalar
  apply hscalar.congr'
  filter_upwards [hf] with k hk
  have hslice : ContDiffOn ℝ ∞ (fun x => f k (t, x)) (Metric.closedBall p ρ) :=
    hk.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => ⟨ht, hx⟩)
  have hsmoothf := hslice.contDiffAt
    (mem_of_superset (Metric.isOpen_ball.mem_nhds hpball) Metric.ball_subset_closedBall)
  exact ((coefficientEval a b).iteratedFDeriv_comp_left hsmoothf hr).symm



theorem tendsto_terminal_curvatureTensorNorm
    (t : ℝ) (ht : t ≤ 0) (x : G.limitCarrier.carrier) :
    Tendsto (fun k => ((S.term (G.subsequence k)).flow.flow.connection t).curvatureTensorNorm
      (G.embedding k x)) atTop (𝓝 ((F.connection t).curvatureTensorNorm x)) := by
  classical
  let c := extChartAt (𝓡 3) x
  let p := c x
  have hp : p ∈ c.target := mem_extChartAt_target x
  have hcx : c.symm p = x := c.left_inv (mem_extChartAt_source x)
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := G.limitCarrier.exists_local_coordinate_realization
    (F.metric t) x t p hp
  have hg : ∀ᶠ y in 𝓝 p, ∀ a b : Fin 3,
      g.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      G.limitCarrier.coordinateCoefficient x
        (fun _ y v w => G.limitCarrier.metricInner (F.metric t) y v w) a b (t, y) :=
    Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  obtain ⟨ρ, hρ, hρc⟩ := G.exists_pos_referenceChartBall_radius x
  have hφ : ∀ᶠ k : ℕ in atTop, ∀ᶠ y in 𝓝 p,
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (G.embedding k ∘ c.symm) y ∧
        Function.Injective (mfderiv (𝓡 3) (𝓡 3) (G.embedding k ∘ c.symm) y) := by
    filter_upwards [S.eventually_embedding_chart_isLocalDiffeomorphAt G x
      (isCompact_closedBall _ _) hρc] with k hk
    filter_upwards [Metric.ball_mem_nhds p (by positivity : 0 < 2 * ρ)] with y hy
    have hd := hk y (Metric.ball_subset_closedBall hy)
    exact ⟨hd.contMDiffAt, (hd.mfderivToContinuousLinearEquiv (by simp)).injective⟩
  have hnorm := LeviCivitaData.tendsto_curvatureTensorNorm_of_moving_scalar_pullback_jets
    (fun k => (S.term (G.subsequence k)).flow.flow.connection t)
    (fun k => G.embedding k ∘ c.symm) D (fun _ : ℕ => p) p hφ (by
      intro r _ a b
      rw [G.limitCarrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
        x _ t p g hg r a b]
      exact S.tendsto_terminal_spatial_pullbackJet G F hF P hcontrol hcomplete x hp ht r a b)
  have hlim : D.curvatureTensorNorm p = (F.connection t).curvatureTensorNorm x := by
    have heqnorm := G.limitCarrier.curvatureTensorNorm_eq_of_coordinate_germ
      (F.metric t) (F.connection t) x t p hp g D hg
    change D.curvatureTensorNorm p = (F.connection t).curvatureTensorNorm (c.symm p) at heqnorm
    rw [hcx] at heqnorm
    exact heqnorm
  rw [hlim] at hnorm
  simpa only [Function.comp_apply, hcx] using hnorm

end PoincareConjecture.NormalizedKappaSolutionSequence
