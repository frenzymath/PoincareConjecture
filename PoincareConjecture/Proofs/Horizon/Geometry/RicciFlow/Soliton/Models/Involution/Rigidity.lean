import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring












set_option autoImplicit false

namespace Poincare.Geometry

theorem real_involutive_isometry_eq_id_or_reflection {f : ℝ → ℝ}
    (hi : Isometry f) (hinv : Function.Involutive f) :
    (∀ x, f x = x) ∨ ∃ c : ℝ, ∀ x, f x = 2 * c - x := by
  have hs (x y : ℝ) : (f x - f y) ^ 2 = (x - y) ^ 2 := by
    have h := congrArg (fun z : ℝ => z ^ 2) (hi.dist_eq x y)
    simpa only [Real.dist_eq, sq_abs] using h
  have hsign : f 1 - f 0 = 1 ∨ f 1 - f 0 = -1 := by
    have h := hs 1 0
    norm_num at h
    exact h
  rcases hsign with hsign | hsign
  · have hformula (x : ℝ) : f x = f 0 + x := by
      have h0 := hs x 0
      have h1 := hs x 1
      nlinarith
    have hzero : f 0 = 0 := by
      have h := hinv 0
      rw [hformula] at h
      linarith
    exact Or.inl (fun x => by simpa [hzero] using hformula x)
  · refine Or.inr ⟨f 0 / 2, ?_⟩
    intro x
    have h0 := hs x 0
    have h1 := hs x 1
    nlinarith

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
private theorem unit_sphere_norm (x : Metric.sphere (0 : E) 1) : ‖(x : E)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

theorem unit_sphere_isometry_inner
    {f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1}
    (hi : Isometry f) (x y : Metric.sphere (0 : E) 1) :
    inner ℝ (f x : E) (f y : E) = inner ℝ (x : E) (y : E) := by
  have h := congrArg (fun z : ℝ => z ^ 2) (hi.dist_eq x y)
  simp only [Subtype.dist_eq, dist_eq_norm] at h
  rw [norm_sub_sq_real, norm_sub_sq_real] at h
  simp only [unit_sphere_norm, one_pow] at h
  linarith

theorem free_involutive_sphere_isometry_eq_antipodal
    {f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1}
    (hi : Isometry f) (hinv : Function.Involutive f) (hfree : ∀ x, f x ≠ x)
    (x : Metric.sphere (0 : E) 1) : f x = -x := by
  classical
  by_contra hnot
  have hsum : (x : E) + (f x : E) ≠ 0 := by
    intro h
    apply hnot
    apply Subtype.ext
    change (f x : E) = -(x : E)
    exact eq_neg_of_add_eq_zero_right h
  let r : ℝ := ‖(x : E) + (f x : E)‖
  have hr : 0 < r := norm_pos_iff.mpr hsum
  let m : Metric.sphere (0 : E) 1 :=
    ⟨r⁻¹ • ((x : E) + (f x : E)), by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      exact inv_mul_cancel₀ (ne_of_gt hr)⟩
  have hmx := unit_sphere_isometry_inner hi m x
  have hmfx := unit_sphere_isometry_inner hi m (f x)
  rw [hinv x] at hmfx
  have hmm : inner ℝ (m : E) (m : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, unit_sphere_norm, one_pow]
  have hfmm : inner ℝ (f m : E) (m : E) = 1 := by
    calc
      inner ℝ (f m : E) (m : E) =
          r⁻¹ * (inner ℝ (f m : E) (x : E) + inner ℝ (f m : E) (f x : E)) := by
            simp only [m, real_inner_smul_right, inner_add_right]
      _ = r⁻¹ * (inner ℝ (m : E) (f x : E) + inner ℝ (m : E) (x : E)) := by
            rw [hmx, hmfx]
      _ = inner ℝ (m : E) (m : E) := by
            change _ = inner ℝ (m : E) (r⁻¹ • ((x : E) + (f x : E)))
            rw [real_inner_smul_right, inner_add_right]
            ring
      _ = 1 := hmm
  have hdist : ‖(f m : E) - (m : E)‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, unit_sphere_norm, unit_sphere_norm, hfmm]
    norm_num
  exact hfree m (Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp
    (sq_eq_zero_iff.mp hdist))))

end Sphere

theorem free_product_involutive_isometry_normal_forms
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1} {g : ℝ → ℝ}
    (hf : Isometry f) (hg : Isometry g)
    (hfi : Function.Involutive f) (hgi : Function.Involutive g)
    (hfree : ∀ x z, (f x, g z) ≠ (x, z)) :
    (∀ x z, (f x, g z) = (-x, z)) ∨
      ∃ c : ℝ, ∀ x z, (f x, g z) = (-x, 2 * c - z) := by
  rcases real_involutive_isometry_eq_id_or_reflection hg hgi with hid | ⟨c, href⟩
  · have hffree (x) : f x ≠ x := by
      intro h
      exact hfree x 0 (Prod.ext h (hid 0))
    exact Or.inl (fun x z => Prod.ext
      (free_involutive_sphere_isometry_eq_antipodal hf hfi hffree x) (hid z))
  · have hffree (x) : f x ≠ x := by
      intro h
      exact hfree x c (Prod.ext h (by rw [href]; ring))
    exact Or.inr ⟨c, fun x z => Prod.ext
      (free_involutive_sphere_isometry_eq_antipodal hf hfi hffree x) (href z)⟩

end Poincare.Geometry
