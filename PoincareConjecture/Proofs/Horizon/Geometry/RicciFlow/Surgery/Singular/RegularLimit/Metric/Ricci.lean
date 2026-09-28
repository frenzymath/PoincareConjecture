import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.RicciConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Scalar


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem tendsto_terminal_ricci
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04) (v w : TangentSpace (𝓡 3) x) :
    Tendsto (fun t => (H.reference.flow.connection t).ricci (x : M) v w) (𝓝[<] T)
      (𝓝 ((H.terminalConnection P04).ricci x v w)) := by
  let p := extChartAt (𝓡 3) x x
  have hp : p ∈ (extChartAt (𝓡 3) x).target := mem_extChartAt_target x
  have hi := Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm
    (I := 𝓡 3) hp
  obtain ⟨a, ha⟩ := hi.surjective v
  obtain ⟨b, hb⟩ := hi.surjective w
  have hjet (m : ℕ) (_hm : m ≤ 2) :=
    (H.tendstoUniformlyOn_terminalMetric_jets P04 x m isCompact_singleton
      (singleton_subset_iff.mpr hp)).tendsto_at (mem_singleton p)
  have h := SingularRegularLimit.tendsto_ricci_of_chart_metric_jets
    H.reference.flow.metric H.reference.flow.connection (H.terminalMetric P04)
    (H.terminalConnection P04) (x : M) x p a b
    (H.regularRegion_chart_target_subset P04 x hp) hp hjet
  have hM : (extChartAt (𝓡 3) (x : M)).symm p = (x : M) := extChartAt_to_inv (x : M)
  have hX : (extChartAt (𝓡 3) x).symm p = x := extChartAt_to_inv x
  have hD := H.regularRegion_chart_mfderiv P04 x hp
  have hDa := (congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
    EuclideanSpace ℝ (Fin 3) => L a) hD).trans ha
  have hDb := (congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
    EuclideanSpace ℝ (Fin 3) => L b) hD).trans hb
  have hsource (t : ℝ) := congrArg
    (fun z : M × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (H.reference.flow.connection t).ricci z.1 z.2.1 z.2.2)
    (show ((extChartAt (𝓡 3) (x : M)).symm p,
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (x : M)).symm p a,
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (x : M)).symm p b) =
        ((x : M), v, w) from Prod.ext hM (Prod.ext hDa hDb))
  have htarget := congrArg
    (fun z : H.regularRegion P04 × EuclideanSpace ℝ (Fin 3) ×
        EuclideanSpace ℝ (Fin 3) => (H.terminalConnection P04).ricci z.1 z.2.1 z.2.2)
    (show ((extChartAt (𝓡 3) x).symm p,
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) x).symm p a,
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) x).symm p b) = (x, v, w) by
      exact Prod.ext hX (Prod.ext ha hb))
  exact htarget ▸ h.congr hsource

end PoincareConjecture.SingularTimeAssumptions
