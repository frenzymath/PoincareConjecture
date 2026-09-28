import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback










set_option autoImplicit false

open Bundle
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in


theorem continuous_euclideanCurvatureTensor {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (u v w z : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => D.curvatureTensor x u v w z) := by
  let X : Fin 4 → (y : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) y :=
    fun i _ => ![u, v, w, z] i
  have hX (i : Fin 4) : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (X i y)) := by
    intro x
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa [X] using
      (contMDiffAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := ![u, v, w, z] i) (x := x))
  have h := D.riemannEvaluation_isSmooth_model.2 Set.univ isOpen_univ X
    (fun i => (hX i).contMDiffOn)
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x : EuclideanSpace ℝ (Fin n) => D.curvatureTensor x u v w z) := by
    simpa [X, LeviCivitaData.riemannEvaluation] using contMDiffOn_univ.mp h
  exact hs.continuous

end PoincareConjecture.M34
