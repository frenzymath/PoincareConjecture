import PoincareConjecture.Proofs.M34.Mathlib.RadialCalculus

set_option autoImplicit false

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radialChristoffel (A B C : ℝ) (x u v : E) : E :=
  A • (inner ℝ x u • v + inner ℝ x v • u) +
    (B * inner ℝ u v) • x + (C * inner ℝ x u * inner ℝ x v) • x

theorem radialChristoffel_pairing (c b A B C : ℝ) (x u v w : E)
    (hr : c + b * ‖x‖ ^ 2 = 1) :
    c * inner ℝ (radialChristoffel A B C x u v) w +
        b * (inner ℝ x (radialChristoffel A B C x u v) * inner ℝ x w) =
      c * A * (inner ℝ x u * inner ℝ v w + inner ℝ x v * inner ℝ u w) +
        B * inner ℝ u v * inner ℝ x w +
        (C + 2 * A * b) * inner ℝ x u * inner ℝ x v * inner ℝ x w := by
  simp only [radialChristoffel, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  linear_combination
    (B * inner ℝ u v * inner ℝ x w +
      C * inner ℝ x u * inner ℝ x v * inner ℝ x w) * hr

theorem radialChristoffel_koszul (c b d e A B C : ℝ) (x u v w : E)
    (hr : c + b * ‖x‖ ^ 2 = 1) (hA : 2 * c * A = d)
    (hB : 2 * B = 2 * b - d) (hC : 2 * (C + 2 * A * b) = e) :
    2 * (c * inner ℝ (radialChristoffel A B C x u v) w +
      b * (inner ℝ x (radialChristoffel A B C x u v) * inner ℝ x w)) =
      (d * inner ℝ x u * inner ℝ v w +
        e * inner ℝ x u * (inner ℝ x v * inner ℝ x w) +
        b * (inner ℝ u v * inner ℝ x w + inner ℝ x v * inner ℝ u w)) +
      (d * inner ℝ x v * inner ℝ w u +
        e * inner ℝ x v * (inner ℝ x w * inner ℝ x u) +
        b * (inner ℝ v w * inner ℝ x u + inner ℝ x w * inner ℝ v u)) -
      (d * inner ℝ x w * inner ℝ u v +
        e * inner ℝ x w * (inner ℝ x u * inner ℝ x v) +
        b * (inner ℝ w u * inner ℝ x v + inner ℝ x u * inner ℝ w v)) := by
  rw [radialChristoffel_pairing c b A B C x u v w hr]
  rw [real_inner_comm u w, real_inner_comm u v, real_inner_comm v w]
  linear_combination
    (inner ℝ x u * inner ℝ v w + inner ℝ x v * inner ℝ u w) * hA +
    (inner ℝ u v * inner ℝ x w) * hB +
    (inner ℝ x u * inner ℝ x v * inner ℝ x w) * hC

end Poincare
