import PoincareConjecture.Statements.Ch04.Continuation
import PoincareConjecture.Proofs.M03.ShortTime
import PoincareConjecture.Proofs.M03.ConnectionNativeTime
import PoincareConjecture.Proofs.M03.CurvatureRateAlgebra
import PoincareConjecture.Proofs.M03.MetricDifferenceEnergyRate
import PoincareConjecture.Proofs.M03.ConnectionRateRicciSmoothness













set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]


theorem ricciFlowContinuation : RicciFlowContinuation n M := by
  intro T hT F hbound
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨gT, _, _, hjets⟩ :=
    Proofs.M03.exists_ricciFlow_endpoint_metric_of_curvature_bound hT F hC
  obtain ⟨δ, hδ, R, hR⟩ := shortTimeRicciFlowExistence gT
  obtain ⟨G, hG⟩ := Proofs.M03.exists_ricciFlow_time_translate hδ R T
  have hGT : G.metric T = gT := by rw [hG T, sub_self, hR]
  obtain ⟨H, hHF, _⟩ :=
    Proofs.M03.exists_ricciFlow_gluing_of_uniform_metric_jets hT hδ F G (by
      intro x0
      dsimp only
      intro q K hK hKU i j
      rw [hGT]
      exact (hjets (T / 2) (by linarith) (by linarith) x0 q K hK hKU).2 i j)
  exact ⟨T + δ, by linarith, H, hHF⟩














theorem ricciFlowLocalTheory : RicciFlowLocalTheory n M := by
  exact ⟨shortTimeRicciFlowExistence, ricciFlowUniqueness, ricciFlowContinuation⟩

end PoincareConjecture
