import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Planar.PairedTriangleDeterminants
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem triangle_boundary_determinant
    (b : Module.Basis (Fin 3) ℝ E) (p : Fin 3 → E) (n : E) (i : Fin 3) :
    b.det ![p (i.succAbove 1) - p (i.succAbove 0),
        p i - p (i.succAbove 0), n] =
      (-1 : ℝ) ^ i.val * b.det ![p 1 - p 0, p 2 - p 0, n] := by
  fin_cases i
  all_goals
    simp [Fin.succAbove, Module.Basis.det_apply, Module.Basis.toMatrix_apply, Matrix.det_fin_three]
    <;> ring

end Geometry
