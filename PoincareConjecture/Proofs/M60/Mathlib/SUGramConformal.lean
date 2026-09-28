import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace PoincareConjecture.M60

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem bilinear_eq_inner_of_conformal_gram (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v)
    (hequal : B (EuclideanSpace.basisFun (Fin 2) ℝ 0) (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      B (EuclideanSpace.basisFun (Fin 2) ℝ 1) (EuclideanSpace.basisFun (Fin 2) ℝ 1))
    (horth : B (EuclideanSpace.basisFun (Fin 2) ℝ 0) (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0)
    (v w : E) :
    B v w = B (EuclideanSpace.basisFun (Fin 2) ℝ 0) (EuclideanSpace.basisFun (Fin 2) ℝ 0) *
      inner ℝ v w := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hcoords (x : E) : x = x 0 • e 0 + x 1 • e 1 := by
    simpa only [e, Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using (e.sum_repr x).symm
  have hreverse : B (e 1) (e 0) = 0 := (hB _ _).trans horth
  calc
    B v w = (v 0 * w 0 + v 1 * w 1) * B (e 0) (e 0) := by
      conv_lhs => rw [hcoords v, hcoords w]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rw [horth, hreverse, ← hequal]
      ring
    _ = _ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial]
      ring

end PoincareConjecture.M60
