import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.RetainedObservation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.ProductCircleObservation

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_observation_with_original_current
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) :
    ∃ (d : ℕ) (e : Q.charts.Point → EuclideanSpace ℝ (Fin d))
      (R : EuclideanSpace ℝ (Fin d) →L[ℝ] LoopPlane),
      ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 d) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := (n + 1) + 1) e ∧
      (∀ q, R (e q) = planarCircleObservation q.1.2) ∧ ∀ q, ‖R (e q)‖ = 1 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  obtain ⟨m, o, S, ho, -, -, hS, hnorm⟩ := circleProduct_observation_with_current P
  obtain ⟨d, e, L, he, hei, hread, hL⟩ := auxiliaryCircle_exists_retained_observation Q o ho
  refine ⟨d, e, S.comp L, he, hei, hread, ?_, ?_⟩
  · intro q
    simp only [ContinuousLinearMap.comp_apply, hL, hS]
  · intro q
    simpa only [ContinuousLinearMap.comp_apply, hL] using hnorm q.1

end PoincareConjecture.M64
