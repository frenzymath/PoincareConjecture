import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# A forward comparison with a guarded quadratic derivative bound

This is the scalar threshold-crossing step in the use of Morgan--Tian,
Lemma 11.2, pp. 268-269, in Lemma 16.8, pp. 372-373. A strict linear
barrier gives a uniform doubling time without a derivative estimate below
the prescribed threshold. See the M44 derivation `02-forward-scalar.md`.
-/

set_option autoImplicit false

open Set

/-- A quadratic upper rate above a threshold gives a short forward doubling
bound. The time increment is the one derived for M44's use of Lemma 11.2. -/
theorem le_two_mul_of_deriv_le_sq_above {f f' : ℝ → ℝ} {a b C M q : ℝ}
    (hC : 0 < C) (hM : 0 < M) (hq : q ≤ M)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ s ∈ Ico a b, HasDerivWithinAt f (f' s) (Ici s) s)
    (hinitial : f a ≤ M)
    (hrate : ∀ s ∈ Ico a b, q ≤ f s → f' s ≤ C * f s ^ 2)
    (htime : 8 * C * M * (b - a) ≤ 1) :
    ∀ s ∈ Icc a b, f s ≤ 2 * M := by
  let B : ℝ → ℝ := fun s => M + 8 * C * M ^ 2 * (s - a)
  have hBbounds (s : ℝ) (hs : s ∈ Icc a b) : M ≤ B s ∧ B s ≤ 2 * M := by
    have hlo : 0 ≤ 8 * C * M ^ 2 * (s - a) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hs.1)
    have htime' : 8 * C * M * (s - a) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 a) (by positivity)).trans htime
    have hhi := mul_le_mul_of_nonneg_right htime' hM.le
    dsimp [B]
    constructor <;> nlinarith
  have hBd (s : ℝ) : HasDerivAt B (8 * C * M ^ 2) s := by
    simpa only [B, id_eq, mul_one] using
      (((hasDerivAt_id s).sub_const a).const_mul (8 * C * M ^ 2)).const_add M
  have hle : ∀ s ∈ Icc a b, f s ≤ B s := by
    apply image_le_of_deriv_right_lt_deriv_boundary hcont hderiv
    · simpa only [B, sub_self, mul_zero, add_zero] using hinitial
    · exact hBd
    · intro s hs heq
      obtain ⟨hlo, hhi⟩ := hBbounds s ⟨hs.1, hs.2.le⟩
      have hflo : M ≤ f s := by rwa [heq]
      have hfhi : f s ≤ 2 * M := by rwa [heq]
      have hsquare : f s ^ 2 ≤ 4 * M ^ 2 := by nlinarith
      have hbound := (hrate s hs (hq.trans hflo)).trans
        (mul_le_mul_of_nonneg_left hsquare hC.le)
      have hpositive : 0 < C * M ^ 2 := mul_pos hC (sq_pos_of_pos hM)
      nlinarith
  intro s hs
  exact (hle s hs).trans (hBbounds s hs).2
