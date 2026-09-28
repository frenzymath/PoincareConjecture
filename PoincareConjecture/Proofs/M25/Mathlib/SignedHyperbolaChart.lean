import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25

theorem exists_signed_hyperbola_chart
    (rho sx sy : ℝ) (hrho : 0 < rho)
    (hsx : sx ^ 2 = 1) (hsy : sy ^ 2 = 1) :
    ∃ X : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      X.source = {p : ℝ × ℝ |
        -1 < p.2 ∧ |p.1| < rho ^ 2 * (1 + p.2) ^ 2} ∧
      X.target = {v : ℝ × ℝ | 0 < sx * v.1 ∧ 0 < sy * v.2} ∧
      (∀ p : ℝ × ℝ, X p =
        (sx * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2),
          sy * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2))) ∧
      (∀ v : ℝ × ℝ, X.symm v =
        (-v.1 ^ 2 + v.2 ^ 2,
          Real.sqrt (v.1 ^ 2 + v.2 ^ 2) / rho - 1)) ∧
      ContDiffOn ℝ ∞ X X.source ∧
      ContDiffOn ℝ ∞ X.symm X.target ∧
      ∀ p ∈ X.source,
        (X p).1 ^ 2 + (X p).2 ^ 2 = rho ^ 2 * (1 + p.2) ^ 2 ∧
        -(X p).1 ^ 2 + (X p).2 ^ 2 = p.1 := by
  let S : Set (ℝ × ℝ) := {p |
    -1 < p.2 ∧ |p.1| < rho ^ 2 * (1 + p.2) ^ 2}
  let T : Set (ℝ × ℝ) := {v | 0 < sx * v.1 ∧ 0 < sy * v.2}
  let F : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (sx * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2),
      sy * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2))
  let G : (ℝ × ℝ) → (ℝ × ℝ) := fun v =>
    (-v.1 ^ 2 + v.2 ^ 2, Real.sqrt (v.1 ^ 2 + v.2 ^ 2) / rho - 1)
  have hroots (p : ℝ × ℝ) (hp : p ∈ S) :
      0 < (rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2 ∧
      0 < (rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2 := by
    have h := abs_lt.mp hp.2
    constructor <;> linarith only [h.1, h.2]
  have hsquares (p : ℝ × ℝ) (hp : p ∈ S) :
      (F p).1 ^ 2 + (F p).2 ^ 2 = rho ^ 2 * (1 + p.2) ^ 2 ∧
      -(F p).1 ^ 2 + (F p).2 ^ 2 = p.1 := by
    dsimp only [F]
    rw [mul_pow, mul_pow, hsx, hsy,
      Real.sq_sqrt (hroots p hp).1.le, Real.sq_sqrt (hroots p hp).2.le]
    constructor <;> ring
  have hF (p : ℝ × ℝ) (hp : p ∈ S) : F p ∈ T := by
    change 0 < sx * (sx * _) ∧ 0 < sy * (sy * _)
    rw [← mul_assoc, ← mul_assoc, ← pow_two sx, ← pow_two sy, hsx, hsy,
      one_mul, one_mul]
    exact ⟨Real.sqrt_pos.mpr (hroots p hp).1,
      Real.sqrt_pos.mpr (hroots p hp).2⟩
  have hleft (p : ℝ × ℝ) (hp : p ∈ S) : G (F p) = p := by
    apply Prod.ext
    · exact (hsquares p hp).2
    · change Real.sqrt ((F p).1 ^ 2 + (F p).2 ^ 2) / rho - 1 = p.2
      rw [(hsquares p hp).1,
        show rho ^ 2 * (1 + p.2) ^ 2 = (rho * (1 + p.2)) ^ 2 by ring,
        Real.sqrt_sq (mul_nonneg hrho.le (by linarith only [hp.1]))]
      field_simp [hrho.ne']
      ring
  have hpositive (v : ℝ × ℝ) (hv : v ∈ T) :
      0 < v.1 ^ 2 ∧ 0 < v.2 ^ 2 := by
    constructor
    · apply sq_pos_of_ne_zero
      intro heq
      simpa only [heq, mul_zero, lt_self_iff_false] using hv.1
    · apply sq_pos_of_ne_zero
      intro heq
      simpa only [heq, mul_zero, lt_self_iff_false] using hv.2
  have hradial (v : ℝ × ℝ) (hv : v ∈ T) :
      rho ^ 2 * (1 + (G v).2) ^ 2 = v.1 ^ 2 + v.2 ^ 2 := by
    calc
      _ = Real.sqrt (v.1 ^ 2 + v.2 ^ 2) ^ 2 := by
        dsimp only [G]
        field_simp [hrho.ne']
        ring
      _ = v.1 ^ 2 + v.2 ^ 2 :=
        Real.sq_sqrt (add_pos (hpositive v hv).1 (hpositive v hv).2).le
  have hG (v : ℝ × ℝ) (hv : v ∈ T) : G v ∈ S := by
    refine ⟨?_, ?_⟩
    · change -1 < Real.sqrt (v.1 ^ 2 + v.2 ^ 2) / rho - 1
      have hpos := div_pos
        (Real.sqrt_pos.mpr (add_pos (hpositive v hv).1 (hpositive v hv).2)) hrho
      linarith only [hpos]
    · rw [hradial v hv]
      change |-v.1 ^ 2 + v.2 ^ 2| < v.1 ^ 2 + v.2 ^ 2
      exact abs_lt.mpr ⟨by linarith only [(hpositive v hv).2],
        by linarith only [(hpositive v hv).1]⟩
  have hsigned (s x : ℝ) (hs : s ^ 2 = 1) (hx : 0 < s * x) :
      s * Real.sqrt (x ^ 2) = x := by
    rcases sq_eq_one_iff.mp hs with rfl | rfl
    · simp only [one_mul] at hx ⊢
      exact Real.sqrt_sq hx.le
    · have hxneg : x < 0 := by linarith only [hx]
      rw [Real.sqrt_sq_eq_abs, abs_of_neg hxneg]
      ring
  have hright (v : ℝ × ℝ) (hv : v ∈ T) : F (G v) = v := by
    apply Prod.ext
    · change sx * Real.sqrt ((rho ^ 2 * (1 + (G v).2) ^ 2 - (G v).1) / 2) = v.1
      rw [hradial v hv]
      rw [show (v.1 ^ 2 + v.2 ^ 2 - (G v).1) / 2 = v.1 ^ 2 by dsimp [G]; ring]
      exact hsigned sx v.1 hsx hv.1
    · change sy * Real.sqrt ((rho ^ 2 * (1 + (G v).2) ^ 2 + (G v).1) / 2) = v.2
      rw [hradial v hv]
      rw [show (v.1 ^ 2 + v.2 ^ 2 + (G v).1) / 2 = v.2 ^ 2 by dsimp [G]; ring]
      exact hsigned sy v.2 hsy hv.2
  have hFs : ContDiffOn ℝ ∞ F S := by
    exact (contDiffOn_const.mul
      ((by fun_prop : ContDiffOn ℝ ∞
        (fun p : ℝ × ℝ => (rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2) S).sqrt
          (fun p hp => (hroots p hp).1.ne'))).prodMk
      (contDiffOn_const.mul
        ((by fun_prop : ContDiffOn ℝ ∞
          (fun p : ℝ × ℝ => (rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2) S).sqrt
            (fun p hp => (hroots p hp).2.ne')))
  have hGs : ContDiffOn ℝ ∞ G T := by
    exact (by fun_prop : ContDiffOn ℝ ∞ (fun v : ℝ × ℝ => -v.1 ^ 2 + v.2 ^ 2) T).prodMk
      ((((by fun_prop : ContDiffOn ℝ ∞
        (fun v : ℝ × ℝ => v.1 ^ 2 + v.2 ^ 2) T).sqrt
          (fun v hv => (add_pos (hpositive v hv).1 (hpositive v hv).2).ne')).div_const
            rho).sub contDiffOn_const)
  have hS : IsOpen S :=
    (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_fst.abs (by fun_prop))
  have hT : IsOpen T :=
    (isOpen_lt continuous_const
      (show Continuous (fun v : ℝ × ℝ => sx * v.1) by fun_prop)).inter
      (isOpen_lt continuous_const
        (show Continuous (fun v : ℝ × ℝ => sy * v.2) by fun_prop))
  let X : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := {
    toFun := F
    invFun := G
    source := S
    target := T
    map_source' := hF
    map_target' := hG
    left_inv' := hleft
    right_inv' := hright
    open_source := hS
    open_target := hT
    continuousOn_toFun := hFs.continuousOn
    continuousOn_invFun := hGs.continuousOn }
  exact ⟨X, rfl, rfl, fun _ => rfl, fun _ => rfl, hFs, hGs, hsquares⟩

end PoincareConjecture.M25
