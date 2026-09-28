import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.Control
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.SmoothLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

noncomputable def terminalCoordinateCoefficients
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : M) (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := by
  classical
  let c := extChartAt (𝓡 3) q
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (c.symm z)) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 3)))
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (c.symm z)) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 3)))
  exact if hz : c.symm z ∈ H.reference.regularLimitSet then
    ContinuousLinearMap.bilinearComp (H.terminalMetricBilinear P04 hz)
      (mfderiv (𝓡 3) (𝓡 3) c.symm z) (mfderiv (𝓡 3) (𝓡 3) c.symm z)
    else 0

theorem terminalCoordinateCoefficients_apply
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : M) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : (extChartAt (𝓡 3) q).symm z ∈ H.reference.regularLimitSet)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    H.terminalCoordinateCoefficients P04 q z v w =
      H.terminalMetricBilinear P04 hz
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z v)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z w) := by
  simp only [terminalCoordinateCoefficients, dif_pos hz,
    ContinuousLinearMap.bilinearComp_apply]
  rfl

theorem tendsto_terminalCoordinateCoefficients
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : M) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : (extChartAt (𝓡 3) q).symm z ∈ H.reference.regularLimitSet) :
    Tendsto (fun t => (H.reference.flow.metric t).pullbackCoefficients
      (extChartAt (𝓡 3) q).symm z) (𝓝[<] T)
        (𝓝 (H.terminalCoordinateCoefficients P04 q z)) := by
  let x := (extChartAt (𝓡 3) q).symm z
  let : NormedAddCommGroup (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 3)))
  let : NormedSpace ℝ (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 3)))
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] TangentSpace (𝓡 3) x :=
    mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z
  have hc : Continuous (fun B : TangentSpace (𝓡 3) x →L[ℝ]
      TangentSpace (𝓡 3) x →L[ℝ] ℝ => (ContinuousLinearMap.precomp ℝ D).comp (B.comp D)) := by
    fun_prop
  convert (hc.tendsto (H.terminalMetricBilinear P04 hz)).comp
    (H.tendsto_terminalMetricBilinear P04 hz) using 1
  · rfl
  · congr 1
    ext v w
    exact H.terminalCoordinateCoefficients_apply P04 q hz v w

theorem exists_smooth_terminal_coordinate_limit
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {q : M} (hq : q ∈ H.reference.regularLimitSet) :
    ∃ r : ℝ, 0 < r ∧
      let c := extChartAt (𝓡 3) q
      Metric.closedBall (c q) r ⊆ c.target ∧
      c.symm '' Metric.closedBall (c q) r ⊆ H.reference.regularLimitSet ∧
      ContDiffOn ℝ ∞ (H.terminalCoordinateCoefficients P04 q) (Metric.ball (c q) r) ∧
      ∀ (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin 3))),
        IsCompact K → K ⊆ Metric.ball (c q) r →
        TendstoUniformlyOn
          (fun t => iteratedFDeriv ℝ m
            ((H.reference.flow.metric t).pullbackCoefficients c.symm))
          (iteratedFDeriv ℝ m (H.terminalCoordinateCoefficients P04 q)) (𝓝[<] T) K := by
  obtain ⟨s, r, _, hsT, hr, htarget, hreg, hbound⟩ :=
    H.exists_uniform_coordinate_metric_jet_tail P04 hq
  let c := extChartAt (𝓡 3) q
  refine ⟨r, hr, htarget, hreg, ?_⟩
  apply SingularRegularLimit.smooth_limit_of_eventual_jet_bounds Metric.isOpen_ball
  · intro z hz
    exact H.tendsto_terminalCoordinateCoefficients P04 q
      (hreg ⟨z, Metric.ball_subset_closedBall hz, rfl⟩)
  · exact Eventually.of_forall fun t =>
      ((H.reference.flow.metric t).contDiffOn_chartCoefficients q).mono
        (Metric.ball_subset_closedBall.trans htarget)
  · intro K _ hK m
    obtain ⟨B, _, hB⟩ := hbound m
    refine ⟨B, ?_⟩
    filter_upwards [Ico_mem_nhdsLT hsT] with t ht z hz
    exact hB t ht z (Metric.ball_subset_closedBall (hK hz))

theorem contDiffAt_terminalCoordinateCoefficients
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {q : M} (hq : q ∈ H.reference.regularLimitSet) :
    ContDiffAt ℝ ∞ (H.terminalCoordinateCoefficients P04 q) ((extChartAt (𝓡 3) q) q) := by
  obtain ⟨r, hr, _, _, hsm, _⟩ := H.exists_smooth_terminal_coordinate_limit P04 hq
  exact hsm.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

end PoincareConjecture.SingularTimeAssumptions
