import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PoincareConjecture

open Classical in

theorem m64Conformal_transverse_bound {ι : Type*} [Fintype ι]
    (G : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hsymm : ∀ v w, G v w = G w v) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hlo : ∀ z : EuclideanSpace ℝ ι, lower * ‖z‖ ^ 2 ≤ G z z)
    (hhi : ∀ z : EuclideanSpace ℝ ι, G z z ≤ upper * ‖z‖ ^ 2)
    (j : ι) (v w : EuclideanSpace ℝ ι)
    (hdiag : G v v = G w w) (hmixed : G v w = 0) :
    ‖v‖ ^ 2 + ‖w‖ ^ 2 ≤ (2 * upper / lower) *
      ∑ i : ι, if i = j then 0 else v i ^ 2 + w i ^ 2 := by
  classical
  let A := v j ^ 2 + w j ^ 2
  let T := ∑ i : ι, if i = j then 0 else v i ^ 2 + w i ^ 2
  have hA : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdecomp : ‖v‖ ^ 2 + ‖w‖ ^ 2 = A + T := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ i : ι, ((if i = j then A else 0) +
          (if i = j then 0 else v i ^ 2 + w i ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, A,
          add_zero, zero_add]
      _ = A + T := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_ite_eq',
          Finset.mem_univ, if_true, T]
  have hfactor : G v v ≤ upper * T := by
    by_cases hzero : A = 0
    · have hv : ‖v‖ ^ 2 ≤ T := by
        rw [hzero, zero_add] at hdecomp
        nlinarith [sq_nonneg ‖w‖]
      exact (hhi v).trans (mul_le_mul_of_nonneg_left hv hupper)
    · have hpos : 0 < A := lt_of_le_of_ne hA (Ne.symm hzero)
      let q : EuclideanSpace ℝ ι := w j • v - v j • w
      have hrev : G w v = 0 := (hsymm w v).trans hmixed
      have hq : G q q = A * G v v := by
        dsimp only [q, A]
        simp only [map_sub, map_smul, sub_apply, smul_apply,
          smul_eq_mul, ← hdiag, hmixed, hrev]
        ring
      have hqi (i : ι) : q i ^ 2 ≤ A * (if i = j then 0 else v i ^ 2 + w i ^ 2) := by
        change (w j * v i - v j * w i) ^ 2 ≤ _
        by_cases hij : i = j
        · subst i
          simp only [ite_true, mul_comm (w j) (v j), sub_self, zero_pow two_ne_zero,
            mul_zero, le_refl]
        · rw [if_neg hij]
          dsimp only [A]
          nlinarith [sq_nonneg (v j * v i + w j * w i)]
      have hqnorm : ‖q‖ ^ 2 ≤ A * T := by
        rw [EuclideanSpace.real_norm_sq_eq]
        calc
          _ ≤ ∑ i : ι, A * (if i = j then 0 else v i ^ 2 + w i ^ 2) :=
            Finset.sum_le_sum fun i _ => hqi i
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
