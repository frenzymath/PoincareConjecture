import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic










set_option autoImplicit false

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]




theorem sq_inner_add_sq_inner_le (u v w : E) {a : ℝ} (ha : 0 < a)
    (hu : inner ℝ u u = a) (hv : inner ℝ v v = a) (huv : inner ℝ u v = 0) :
    (inner ℝ w u) ^ 2 + (inner ℝ w v) ^ 2 ≤ a * inner ℝ w w := by
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  have huw : inner ℝ u w = inner ℝ w u := real_inner_comm _ _
  have hvw : inner ℝ v w = inner ℝ w v := real_inner_comm _ _
  have h := mul_nonneg ha.le (real_inner_self_nonneg
    (x := w - (inner ℝ w u / a) • u - (inner ℝ w v / a) • v))
  have heq : a * inner ℝ (w - (inner ℝ w u / a) • u - (inner ℝ w v / a) • v)
      (w - (inner ℝ w u / a) • u - (inner ℝ w v / a) • v) =
      a * inner ℝ w w - (inner ℝ w u) ^ 2 - (inner ℝ w v) ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hu, hv, huv, hvu, huw, hvw]
    field_simp
    ring
  rw [heq] at h
  linarith





theorem conformal_tracefree_hessian_bound (u v A B : E) {a x y : ℝ}
    (ha : 0 < a) (hu : inner ℝ u u = a) (hv : inner ℝ v v = a)
    (huv : inner ℝ u v = 0)
    (hAu : inner ℝ A u = x / 2) (hAv : inner ℝ A v = -y / 2)
    (hBu : inner ℝ B u = y / 2) (hBv : inner ℝ B v = x / 2) :
    (x ^ 2 + y ^ 2) / a ≤ 2 * (inner ℝ A A + inner ℝ B B) := by
  have hA := sq_inner_add_sq_inner_le u v A ha hu hv huv
  have hB := sq_inner_add_sq_inner_le u v B ha hu hv huv
  rw [hAu, hAv] at hA
  rw [hBu, hBv] at hB
  apply (div_le_iff₀ ha).mpr
  nlinarith

end PoincareConjecture.M60
