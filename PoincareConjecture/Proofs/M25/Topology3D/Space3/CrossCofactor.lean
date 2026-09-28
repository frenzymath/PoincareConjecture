import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

namespace PoincareConjecture.M25.Topology3D

theorem mulVec_crossProduct_cofactor (A : Matrix (Fin 3) (Fin 3) ℝ)
    (u v : Fin 3 → ℝ) :
    crossProduct (A *ᵥ u) (A *ᵥ v) =
      A.adjugate.transpose *ᵥ crossProduct u v := by
  ext i
  fin_cases i <;>
    simp [cross_apply, Matrix.mulVec, Matrix.vec3_dotProduct,
      Matrix.adjugate_fin_three, Matrix.transpose_apply] <;> ring

theorem contDiff_adjugate_fin_three :
    ContDiff ℝ ∞ (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.adjugate) := by
  have h (i j : Fin 3) :
      ContDiff ℝ ∞ (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) :=
    contDiff_apply_apply ℝ ℝ i j
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp_rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply] <;>
    first
    | exact ((h _ _).mul (h _ _)).sub ((h _ _).mul (h _ _))
    | exact ((h _ _).mul (h _ _)).neg.add ((h _ _).mul (h _ _))

theorem contDiff_adjugate_transpose_mulVec :
    ContDiff ℝ ∞
      (fun z : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) =>
        z.1.adjugate.transpose *ᵥ z.2) := by
  have hA : ContDiff ℝ ∞
      (fun z : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) => z.1.adjugate) :=
    contDiff_adjugate_fin_three.comp contDiff_fst
  have hm (j i : Fin 3) : ContDiff ℝ ∞
      (fun z : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) => z.1.adjugate j i) :=
    (contDiff_apply_apply ℝ ℝ j i).comp hA
  have hv (j : Fin 3) : ContDiff ℝ ∞
      (fun z : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) => z.2 j) :=
    (contDiff_apply ℝ ℝ j).comp contDiff_snd
  refine contDiff_pi.2 fun i => ?_
  simpa only [Matrix.mulVec, Matrix.vec3_dotProduct, Matrix.transpose_apply] using
    (((hm 0 i).mul (hv 0)).add ((hm 1 i).mul (hv 1))).add ((hm 2 i).mul (hv 2))

end PoincareConjecture.M25.Topology3D
