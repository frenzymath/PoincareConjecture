import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic









set_option autoImplicit false

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem sq_bilinear_add_sq_bilinear_le (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ u v, B u v = B v u) (hnonneg : ∀ w, 0 ≤ B w w)
    (u v w : E) {a : ℝ} (ha : 0 < a)
    (hu : B u u = a) (hv : B v v = a) (huv : B u v = 0) :
    (B w u) ^ 2 + (B w v) ^ 2 ≤ a * B w w := by
  have hvu : B v u = 0 := by rw [hsymm, huv]
  have huw : B u w = B w u := hsymm _ _
  have hvw : B v w = B w v := hsymm _ _
  have h := mul_nonneg ha.le (hnonneg (w - (B w u / a) • u - (B w v / a) • v))
  have heq : a * B (w - (B w u / a) • u - (B w v / a) • v)
      (w - (B w u / a) • u - (B w v / a) • v) =
      a * B w w - (B w u) ^ 2 - (B w v) ^ 2 := by
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul,
      hu, hv, huv, hvu, huw, hvw]
    field_simp
    ring
  rw [heq] at h
  linarith




theorem conformal_bilinear_hessian_bound (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ u v, G u v = G v u) (hnonneg : ∀ w, 0 ≤ G w w)
    (u v A B : E) {a x y : ℝ}
    (ha : 0 < a) (hu : G u u = a) (hv : G v v = a) (huv : G u v = 0)
    (hAu : G A u = x / 2) (hAv : G A v = -y / 2)
    (hBu : G B u = y / 2) (hBv : G B v = x / 2) :
    (x ^ 2 + y ^ 2) / a ≤ 2 * (G A A + G B B) := by
  have hA := sq_bilinear_add_sq_bilinear_le G hsymm hnonneg u v A ha hu hv huv
  have hB := sq_bilinear_add_sq_bilinear_le G hsymm hnonneg u v B ha hu hv huv
  rw [hAu, hAv] at hA
  rw [hBu, hBv] at hB
  apply (div_le_iff₀ ha).mpr
  nlinarith

end PoincareConjecture.M60
