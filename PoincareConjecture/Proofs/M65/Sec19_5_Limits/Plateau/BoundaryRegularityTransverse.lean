import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import Mathlib.Analysis.InnerProductSpace.PiL2











set_option autoImplicit false

namespace PoincareConjecture

private theorem boundary_norm_sq (v : LoopAmbient) :
    ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]





theorem m65Boundary_transverse_derivative_bound
    (G : LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (hsymm : ∀ v w, G v w = G w v) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hlo : ∀ z : LoopAmbient, lower * ‖z‖ ^ 2 ≤ G z z)
    (hhi : ∀ z : LoopAmbient, G z z ≤ upper * ‖z‖ ^ 2)
    (v w : LoopAmbient) (hdiag : G v v = G w w) (hmixed : G v w = 0) :
    ‖v‖ ^ 2 + ‖w‖ ^ 2 ≤ (2 * upper / lower) *
      (v 0 ^ 2 + v 1 ^ 2 + w 0 ^ 2 + w 1 ^ 2) := by
  let A := v 2 ^ 2 + w 2 ^ 2
  let T := v 0 ^ 2 + v 1 ^ 2 + w 0 ^ 2 + w 1 ^ 2
  have hA : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfactor : G v v ≤ upper * T := by
    by_cases hzero : A = 0
    · have hv : v 2 = 0 := by dsimp only [A] at hzero; nlinarith [sq_nonneg (w 2)]
      have hw : w 2 = 0 := by dsimp only [A] at hzero; nlinarith [sq_nonneg (v 2)]
      have hh := hhi v
      rw [boundary_norm_sq, hv] at hh
      have hrest : 0 ≤ upper * (w 0 ^ 2 + w 1 ^ 2) :=
        mul_nonneg hupper (add_nonneg (sq_nonneg _) (sq_nonneg _))
      dsimp only [T]
      nlinarith
    · have hpos : 0 < A := lt_of_le_of_ne hA (Ne.symm hzero)
      let q : LoopAmbient := w 2 • v - v 2 • w
      have hrev : G w v = 0 := (hsymm w v).trans hmixed
      have hq : G q q = A * G v v := by
        dsimp only [q, A]
        simp only [map_sub, map_smul, sub_apply,
          smul_apply, smul_eq_mul, ← hdiag, hmixed, hrev]
        ring
      have hqcoord (i : Fin 3) : q i = w 2 * v i - v 2 * w i := rfl
      have hqnorm : ‖q‖ ^ 2 ≤ A * T := by
        rw [boundary_norm_sq, hqcoord 0, hqcoord 1, hqcoord 2]
        dsimp only [A, T]
        nlinarith [sq_nonneg (v 2 * v 0 + w 2 * w 0),
          sq_nonneg (v 2 * v 1 + w 2 * w 1)]
      have hh : A * G v v ≤ A * (upper * T) := by
        calc
          _ = G q q := hq.symm
          _ ≤ upper * ‖q‖ ^ 2 := hhi q
          _ ≤ upper * (A * T) := mul_le_mul_of_nonneg_left hqnorm hupper
          _ = _ := by ring
      nlinarith
  have hsum := add_le_add (hlo v) (hlo w)
  rw [← hdiag] at hsum
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlower).mpr
  change (‖v‖ ^ 2 + ‖w‖ ^ 2) * lower ≤ 2 * upper * T
  nlinarith




theorem m65Boundary_transverse_derivative_bound_axis
    (G : LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (hsymm : ∀ v w, G v w = G w v) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hlo : ∀ z : LoopAmbient, lower * ‖z‖ ^ 2 ≤ G z z)
    (hhi : ∀ z : LoopAmbient, G z z ≤ upper * ‖z‖ ^ 2)
    (j : Fin 3) (v w : LoopAmbient) (hdiag : G v v = G w w) (hmixed : G v w = 0) :
    ‖v‖ ^ 2 + ‖w‖ ^ 2 ≤ (2 * upper / lower) *
      ∑ i : Fin 3, if i = j then 0 else v i ^ 2 + w i ^ 2 := by
  classical
  let A := v j ^ 2 + w j ^ 2
  let T := ∑ i : Fin 3, if i = j then 0 else v i ^ 2 + w i ^ 2
  have hA : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdecomp : ‖v‖ ^ 2 + ‖w‖ ^ 2 = A + T := by
    dsimp only [A, T]
    rw [boundary_norm_sq, boundary_norm_sq]
    fin_cases j <;> simp [Fin.sum_univ_three] <;> ring
  have hfactor : G v v ≤ upper * T := by
    by_cases hzero : A = 0
    · have hv : ‖v‖ ^ 2 ≤ T := by rw [hzero, zero_add] at hdecomp; nlinarith [sq_nonneg ‖w‖]
      exact (hhi v).trans (mul_le_mul_of_nonneg_left hv hupper)
    · have hpos : 0 < A := lt_of_le_of_ne hA (Ne.symm hzero)
      let q : LoopAmbient := w j • v - v j • w
      have hrev : G w v = 0 := (hsymm w v).trans hmixed
      have hq : G q q = A * G v v := by
        dsimp only [q, A]
        simp only [map_sub, map_smul, sub_apply, smul_apply,
          smul_eq_mul, ← hdiag, hmixed, hrev]
        ring
      have hqi (i : Fin 3) : q i ^ 2 ≤ A * (if i = j then 0 else v i ^ 2 + w i ^ 2) := by
        change (w j * v i - v j * w i) ^ 2 ≤ _
        by_cases hij : i = j
        · subst i
          simp [mul_comm]
        · rw [if_neg hij]
          dsimp only [A]
          nlinarith [sq_nonneg (v j * v i + w j * w i)]
      have hqnorm : ‖q‖ ^ 2 ≤ A * T := by
        rw [EuclideanSpace.real_norm_sq_eq]
        calc
          _ ≤ ∑ i : Fin 3, A * (if i = j then 0 else v i ^ 2 + w i ^ 2) :=
            Finset.sum_le_sum (fun i _ => hqi i)
          _ = A * T := (Finset.mul_sum _ _ _).symm
      have hh : A * G v v ≤ A * (upper * T) := by
        calc
          _ = G q q := hq.symm
          _ ≤ upper * ‖q‖ ^ 2 := hhi q
          _ ≤ upper * (A * T) := mul_le_mul_of_nonneg_left hqnorm hupper
          _ = _ := by ring
      nlinarith
  have hsum := add_le_add (hlo v) (hlo w)
  rw [← hdiag] at hsum
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlower).mpr
  change (‖v‖ ^ 2 + ‖w‖ ^ 2) * lower ≤ 2 * upper * T
  nlinarith

end PoincareConjecture
