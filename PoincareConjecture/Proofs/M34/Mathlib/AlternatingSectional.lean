import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

namespace MultilinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem sectional_scale
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hfirst : ∀ a b c d, A ![a, b, c, d] = -A ![b, a, c, d])
    (hlast : ∀ a b c d, A ![a, b, c, d] = -A ![a, b, d, c])
    (p q : E) (r d s : ℝ) :
    A ![r • p, d • p + s • q, r • p, d • p + s • q] =
      r ^ 2 * s ^ 2 * A ![p, q, p, q] := by
  have hs0 (a b c f : E) (z : ℝ) :
      A ![z • a, b, c, f] = z * A ![a, b, c, f] := by
    simpa only [Matrix.vecCons, smul_eq_mul] using A.cons_smul ![b, c, f] z a
  have hs1 (a b c f : E) (z : ℝ) :
      A ![a, z • b, c, f] = z * A ![a, b, c, f] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons, smul_eq_mul] using
      (A.curryLeft a).cons_smul ![c, f] z b
  have hs2 (a b c f : E) (z : ℝ) :
      A ![a, b, z • c, f] = z * A ![a, b, c, f] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons, smul_eq_mul] using
      ((A.curryLeft a).curryLeft b).cons_smul ![f] z c
  have hs3 (a b c f : E) (z : ℝ) :
      A ![a, b, c, z • f] = z * A ![a, b, c, f] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons, smul_eq_mul] using
      (((A.curryLeft a).curryLeft b).curryLeft c).cons_smul ![] z f
  have ha1 (a b c f z : E) :
      A ![a, b + c, f, z] = A ![a, b, f, z] + A ![a, c, f, z] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
      (A.curryLeft a).cons_add ![f, z] b c
  have ha3 (a b c f z : E) :
      A ![a, b, c, f + z] = A ![a, b, c, f] + A ![a, b, c, z] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
      (((A.curryLeft a).curryLeft b).curryLeft c).cons_add ![] f z
  have hf (a b c : E) : A ![a, a, b, c] = 0 := by
    linarith only [hfirst a a b c]
  have hl (a b c : E) : A ![a, b, c, c] = 0 := by
    linarith only [hlast a b c c]
  simp only [hs0, hs2, ha1, ha3, hs1, hs3, hf, hl]
  ring

theorem sectional_nonneg_of_orthonormal
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hfirst : ∀ a b c d, A ![a, b, c, d] = -A ![b, a, c, d])
    (hlast : ∀ a b c d, A ![a, b, c, d] = -A ![a, b, d, c])
    (hunit : ∀ p q : E, ‖p‖ = 1 → ‖q‖ = 1 → inner ℝ p q = 0 →
      0 ≤ A ![p, q, p, q]) (u v : E) : 0 ≤ A ![u, v, u, v] := by
  by_cases hu : u = 0
  · subst u
    rw [A.map_coord_zero (0 : Fin 4) rfl]
  let r := ‖u‖
  let p := r⁻¹ • u
  have hp : ‖p‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
  have hup : u = r • p := by
    simp [p, r, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu)]
  let d := inner ℝ p v
  let w := v - d • p
  have hvw : v = d • p + w := by dsimp only [w]; abel
  have hpw : inner ℝ p w = 0 := by
    simp [w, d, inner_sub_right, inner_smul_right, hp]
  by_cases hw : w = 0
  · have hv0 : v = d • p + (0 : ℝ) • (0 : E) := by simpa [hw] using hvw
    rw [congrArg₂ (fun a b => A ![a, b, a, b]) hup hv0,
      sectional_scale A hfirst hlast p 0 r d 0]
    simp
  let s := ‖w‖
  let q := s⁻¹ • w
  have hq : ‖q‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hw
  have hpq : inner ℝ p q = 0 := by simp [q, inner_smul_right, hpw]
  have hwq : w = s • q := by
    simp [q, s, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hvq : v = d • p + s • q := by rw [← hwq]; exact hvw
  rw [congrArg₂ (fun a b => A ![a, b, a, b]) hup hvq,
    sectional_scale A hfirst hlast p q r d s]
  exact mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg s)) (hunit p q hp hq hpq)

end MultilinearMap
