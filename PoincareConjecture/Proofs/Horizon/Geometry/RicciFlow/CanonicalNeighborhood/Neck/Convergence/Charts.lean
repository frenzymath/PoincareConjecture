import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Transition









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture

theorem roundCylinderGram_eq_stereographic_formula
    (u : ℝ) (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (a b : Fin 3) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
      2 * (1 - u) * (16 / (‖p.1‖ ^ 2 + 4) ^ 2) *
        ⟪(roundCylinderCoordinateBasis a).1, (roundCylinderCoordinateBasis b).1⟫_ℝ +
        (roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2 := by
  change 2 * (1 - u) * (roundSphereMetric 2).inner
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1)
    (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1
      (roundCylinderCoordinateBasis a).1)
    (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1
      (roundCylinderCoordinateBasis b).1) + _ = _
  rw [roundSphereMetric_chart_symm_inner]
  ring

theorem roundCylinderGram_eq_chart_center
    (u : ℝ) (p q : UnitTwoSphere) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) =
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) p) := by
  funext x a b
  rw [roundCylinderGram_eq_stereographic_formula, roundCylinderGram_eq_stereographic_formula]

theorem roundCylinderChristoffel_eq_chart_center
    (u : ℝ) (p q : UnitTwoSphere) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) =
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) p) := by
  funext x a b d
  simp only [roundCylinderChristoffel, roundCylinderGram_eq_chart_center u p q]

theorem roundCylinderTensorNormSquared_eq_chart_center
    (u : ℝ) (p q : UnitTwoSphere) (x : RoundCylinderCoordinates)
    {r : ℕ} (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) x T =
      roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) p) x T := by
  simp only [roundCylinderTensorNormSquared, roundCylinderGram_eq_chart_center u p q]

end PoincareConjecture
