import PoincareConjecture.Proofs.M35.Thm12_28.CylinderSecondJet

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RoundCylinderClose

theorem contDiffAt_coefficient {epsilon u : ℝ} {B : RoundCylinderTwoTensor}
    (h : RoundCylinderClose epsilon u B) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) (hp : p.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a b : Fin 3) :
    ContDiffAt ℝ ∞ (fun p : RoundCylinderCoordinates =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) p := by
  apply (h.1 q a b).contDiffAt
  apply ((chartAt (EuclideanSpace ℝ (Fin 2)) q).open_target.prod isOpen_Ioo).mem_nhds
  refine ⟨?_, hp⟩
  rw [M35.sphere_chart_target]
  trivial

theorem first_component_sq_lt {epsilon u : ℝ} {B : RoundCylinderTwoTensor}
    (h : RoundCylinderClose epsilon u B) (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hk : 1 ≤ ⌊epsilon⁻¹⌋₊) (a : Fin 3 → Fin 3) :
    (∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i)) *
      (fderiv ℝ (fun p : RoundCylinderCoordinates => roundCylinderTensorCoefficient B
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (a 1) (a 2)) (0, s)
        (roundCylinderCoordinateBasis (a 0))) ^ 2 < epsilon ^ 2 := by
  have hjet := h.component_sq_lt hu (z := (q, s)) hs hk a
  dsimp only at hjet
  rw [M35.sphere_chart_center] at hjet
  rw [M35.roundCylinderIteratedDerivative_one_center u q s B a
    ((h.contDiffAt_coefficient q (0, s) hs (a 1) (a 2)).differentiableAt (by simp))]
    at hjet
  exact hjet

end PoincareConjecture.RoundCylinderClose
