import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The conformal bilinear form determined by its two Gram columns

Equal-length orthogonal standard columns determine a scalar Euclidean
form. This is the final algebraic step in the Hopf argument of
Sacks-Uhlenbeck Corollary 1.7, printed p. 5.
-/

set_option autoImplicit false

namespace PoincareMT.M60

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- A symmetric plane form with equal diagonal entries and zero mixed
entry is its first diagonal times the Euclidean inner product.
Source: SU Corollary 1.7, p. 5; MT Lemma 18.10, pp. 424-426. -/
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

end PoincareMT.M60
