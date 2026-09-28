import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.EmbeddingConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.FlowRealization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.PartialCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.TerminalPositivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Gluing
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalConstructionConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)



theorem exists_terminal_referenceChartBall_flow
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {ρ : ℝ} (hρ : 0 < ρ)
    (hchart : closedBall (extChartAt (𝓡 3) q q) ρ ⊆ (extChartAt (𝓡 3) q).target) :
    ∃ F : RicciFlow 3 (G.referenceChartBall q ρ) (Iic 0),
      ∀ t : ℝ, t < 0 → ∀ (x : G.referenceChartBall q ρ)
        (v w : TangentSpace (𝓡 3) x),
        (F.metric t).inner x v w =
          (G.limitFlow.metric (t + 1)).inner (G.referenceChartBallMap q ρ x)
            (mfderiv (𝓡 3) (𝓡 3) (G.referenceChartBallMap q ρ) x v)
            (mfderiv (𝓡 3) (𝓡 3) (G.referenceChartBallMap q ρ) x w) := by
  let c := extChartAt (𝓡 3) q
  let U := G.referenceChartBall q ρ
  obtain ⟨B, hB, hjet⟩ := S.exists_smooth_terminal_embedding_coefficients
    G P hcontrol hcomplete q hρ hchart
  obtain ⟨hsymm, hlower⟩ := S.terminal_coefficients_symmetric_positive_of_zero_jets
    G P hcontrol hcomplete q (isCompact_closedBall (c q) ρ) hchart B (hjet 0)
  obtain ⟨F, hF⟩ := RicciFlow.exists_ancient_limit_of_eventual_partial_chart_coefficients
    (fun k => (S.term (G.subsequence k)).carrier) hρ
    (fun k => (S.term (G.subsequence k)).flow.flow)
    (G.embeddingChartPartialDiffeomorph q)
    (G.eventually_subset_embeddingChartPartialDiffeomorph_source q
      (isCompact_closedBall (c q) ρ) hchart) U (subset_refl _) B hB
    (fun t ht x hx => hsymm t ht x (ball_subset_closedBall hx))
    (fun t ht x hx => hlower t ht x (ball_subset_closedBall hx)) hjet
  refine ⟨F, ?_⟩
  intro t ht x v w
  have hx : (x : EuclideanSpace ℝ (Fin 3)) ∈ closedBall (c q) ρ :=
    ball_subset_closedBall x.property
  have hBvalue := AncientCompactness.tendsto_of_compact_zero_jets _ B
    (Iic 0 ×ˢ closedBall (c q) ρ) (hjet 0) (z := (t, (x : EuclideanSpace ℝ (Fin 3))))
    ⟨ht.le, hx⟩
  have hinterior := (S.tendstoUniformlyOn_embedding_bilinear_metricJet_unshifted G q 0
    (K := {(t, (x : EuclideanSpace ℝ (Fin 3)))}) isCompact_singleton
    (fun z hz => by rcases mem_singleton_iff.mp hz with rfl; exact ht)
    (fun z hz => by rcases mem_singleton_iff.mp hz with rfl; exact hchart hx)).tendsto_at
      (mem_singleton _)
  have hvalue := (continuous_eval_const
    (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin 3))).continuousAt.tendsto.comp hinterior
  simp only [iteratedFDeriv_zero_apply] at hvalue
  have heq : B (t, (x : EuclideanSpace ℝ (Fin 3))) =
      (G.limitFlow.metric (t + 1)).pullbackCoefficients c.symm x :=
    tendsto_nhds_unique hBvalue hvalue
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q (hchart hx)).contMDiffAt
    (extChartAt_target_mem_nhds' (hchart hx))
  have hd := Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_restrict
    U c.symm (x := x) (hc.mdifferentiableAt (by simp))
  rw [hF t ht.le x v w, heq]
  change (G.limitFlow.metric (t + 1)).inner (c.symm x)
    (mfderiv (𝓡 3) (𝓡 3) c.symm (x : EuclideanSpace ℝ (Fin 3)) v)
    (mfderiv (𝓡 3) (𝓡 3) c.symm (x : EuclideanSpace ℝ (Fin 3)) w) =
    (G.limitFlow.metric (t + 1)).inner (c.symm x)
      (mfderiv (𝓡 3) (𝓡 3) (fun y : U => c.symm y) x v)
      (mfderiv (𝓡 3) (𝓡 3) (fun y : U => c.symm y) x w)
  rw [hd]
  rfl



theorem exists_terminal_flow_on_interior_carrier
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    ∃ F : RicciFlow 3 G.limitCarrier.carrier (Iic 0),
      ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1) := by
  classical
  choose ρ hρ hchart using G.exists_pos_referenceChartBall_radius
  have hsmall (q : G.limitCarrier.carrier) :
      closedBall (extChartAt (𝓡 3) q q) (ρ q) ⊆ (extChartAt (𝓡 3) q).target :=
    (closedBall_subset_closedBall (by linarith [hρ q] : ρ q ≤ 2 * ρ q)).trans (hchart q)
  choose Fchart hFchart using fun q => S.exists_terminal_referenceChartBall_flow
    G P hcontrol hcomplete q (hρ q) (hsmall q)
  let Fneg : RicciFlow 3 G.limitCarrier.carrier (Iio 0) :=
    G.limitFlow.translate 1 (by
      rintro _ ⟨t, ht, rfl⟩
      exact show t + 1 < 1 by have := ht; change t < 0 at this; linarith)
      ordConnected_Iio ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩
  obtain ⟨F, hF, _⟩ := RicciFlow.exists_terminal_extension_of_covering_chart_flows
    Fneg Fchart (fun q => G.referenceChartBallMap q (ρ q))
    (fun q => G.referenceChartBallMap_isLocalDiffeomorph q (ρ q)
      (ball_subset_closedBall.trans (hsmall q)))
    (G.referenceChartBallMap_covers ρ hρ) (fun t ht q x v w => hFchart q t ht x v w)
  exact ⟨F, hF⟩

end PoincareConjecture.NormalizedKappaSolutionSequence
