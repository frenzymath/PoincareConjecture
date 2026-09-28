import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.SpacetimeBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.BoundarySmooth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.Convergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

def extendedCoordinateCoefficients
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : M) (p : ℝ × EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  if p.1 = T then H.terminalCoordinateCoefficients P04 q p.2
  else (H.reference.flow.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm p.2

theorem exists_smooth_terminal_spacetime_coordinates
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {q : M} (hq : q ∈ H.reference.regularLimitSet) :
    ∃ s r : ℝ, H.reference.tMinus < s ∧ s < T ∧ 0 < r ∧
      let c := extChartAt (𝓡 3) q
      Metric.closedBall (c q) r ⊆ c.target ∧
      c.symm '' Metric.closedBall (c q) r ⊆ H.reference.regularLimitSet ∧
      ContDiffOn ℝ ∞ (H.extendedCoordinateCoefficients P04 q)
        (Ioc s T ×ˢ Metric.ball (c q) r) := by
  obtain ⟨s, r, hs, hsT, hr, htarget, hreg, hbound⟩ :=
    H.exists_uniform_coordinate_spacetime_jet_tail P04 hq
  let c := extChartAt (𝓡 3) q
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow H.reference.flow
    (show Ioo s T ⊆ Ico H.reference.tMinus T from
      fun _ ht => ⟨(hs.trans ht.1).le, ht.2⟩)
    ordConnected_Ioo ⟨(2 * s + T) / 3, ⟨by linarith, by linarith⟩,
      (s + 2 * T) / 3, ⟨by linarith, by linarith⟩, by linarith⟩
  refine ⟨s, r, hs, hsT, hr, htarget, hreg, ?_⟩
  apply SingularRegularLimit.contDiffOn_terminal_extension_of_jet_bounds
    hsT Metric.isOpen_ball (convex_ball _ _) (f := fun p =>
      (H.reference.flow.metric p.1).pullbackCoefficients c.symm p.2)
  · exact (G.contDiffOn_pullbackCoefficients isOpen_Ioo (isOpen_extChartAt_target q)
      (contMDiffOn_extChartAt_symm q)).mono
      (fun _ hp => ⟨hp.1, htarget (Metric.ball_subset_closedBall hp.2)⟩)
  · intro m
    obtain ⟨B, _, hb⟩ := hbound m
    exact ⟨B, fun p hp => hb p.1 hp.1 p.2 (Metric.ball_subset_closedBall hp.2)⟩
  · intro x hx
    exact H.tendsto_terminalCoordinateCoefficients P04 q
      (hreg ⟨x, Metric.ball_subset_closedBall hx, rfl⟩)

end PoincareConjecture.SingularTimeAssumptions
