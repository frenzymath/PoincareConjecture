import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.QuadraticReaction

set_option autoImplicit false

open scoped BigOperators

namespace Poincare.RicciFlow.Harnack

variable {I : Type*} [DecidableEq I]

noncomputable def twoFormIdentity (a b c d : I) : ℝ :=
  ((if a = c ∧ b = d then 1 else 0) - (if a = d ∧ b = c then 1 else 0)) / 2

lemma twoFormIdentity_skew_first (a b c d : I) :
    twoFormIdentity a b c d = -twoFormIdentity b a c d := by
  simp only [twoFormIdentity, and_comm]
  ring

lemma twoFormIdentity_skew_last (a b c d : I) :
    twoFormIdentity a b c d = -twoFormIdentity a b d c := by
  dsimp only [twoFormIdentity]
  ring

lemma twoFormIdentity_pair_swap (a b c d : I) :
    twoFormIdentity a b c d = twoFormIdentity c d a b := by
  simp only [twoFormIdentity, eq_comm, and_comm]

lemma twoFormIdentity_bianchi (a b c d : I) :
    twoFormIdentity a b c d + twoFormIdentity b c a d + twoFormIdentity c a b d = 0 := by
  simp only [twoFormIdentity, eq_comm, and_comm]
  ring

lemma abs_twoFormIdentity_le_one (a b c d : I) :
    |twoFormIdentity a b c d| ≤ 1 := by
  unfold twoFormIdentity
  split_ifs <;> norm_num

variable [Fintype I]

lemma twoFormIdentity_contract (U : I → I → ℝ)
    (hU : ∀ a b, U a b = -U b a) (a b : I) :
    (∑ c, ∑ d, twoFormIdentity a b c d * U c d) = U a b := by
  simp only [twoFormIdentity, sub_div, sub_mul, Finset.sum_sub_distrib]
  simp only [ite_and, ite_div, zero_div, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]
  rw [hU b a]
  ring

lemma twoFormIdentity_quadratic (U : I → I → ℝ)
    (hU : ∀ a b, U a b = -U b a) :
    (∑ a, ∑ b, ∑ c, ∑ d, twoFormIdentity a b c d * U a b * U c d) =
      ∑ a, ∑ b, (U a b) ^ 2 := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = U a b * ∑ c, ∑ d, twoFormIdentity a b c d * U c d := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [twoFormIdentity_contract U hU]; ring

private lemma abs_mul_pair_le (A u v C : ℝ) (hC : 0 ≤ C) (hA : |A| ≤ C) :
    |A * u * v| ≤ C / 2 * (u ^ 2 + v ^ 2) := by
  have hprod := mul_le_mul_of_nonneg_right hA (abs_nonneg (u * v))
  have hquad : |u * v| ≤ (u ^ 2 + v ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith only [sq_nonneg (|u| - |v|), sq_abs u, sq_abs v]
  have h := mul_le_mul_of_nonneg_left hquad hC
  rw [abs_mul, ← mul_assoc] at hprod
  rw [abs_mul] at h
  simpa only [abs_mul, mul_assoc] using hprod.trans (by nlinarith only [h])

private lemma abs_mul_shift_error_le
    (r m i d α ψ KR KM : ℝ)
    (hα : 0 ≤ α) (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1)
    (hKR : 0 ≤ KR) (_hKM : 0 ≤ KM)
    (hr : |r| ≤ KR) (hm : |m| ≤ KM) (hi : |i| ≤ 1) (hd : |d| ≤ 1) :
    |(r + ψ * i) * (m + α * d) - r * m| ≤ (KR + 1) * α + KM * ψ := by
  have hiψ : |ψ * i| ≤ ψ := by
    rw [abs_mul, abs_of_nonneg hψ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hψ
  have hdα : |α * d| ≤ α := by
    rw [abs_mul, abs_of_nonneg hα]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hα
  have h₁ : |r * (α * d)| ≤ KR * α := by
    rw [abs_mul]
    exact mul_le_mul hr hdα (abs_nonneg _) hKR
  have h₂ : |ψ * i * m| ≤ ψ * KM := by
    rw [abs_mul]
    exact mul_le_mul hiψ hm (abs_nonneg _) hψ
  have h₃ : |ψ * i * (α * d)| ≤ α := by
    rw [abs_mul]
    exact (mul_le_mul hiψ hdα (abs_nonneg _) hψ).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hψone hα])
  calc
    _ = |r * (α * d) + ψ * i * m + ψ * i * (α * d)| := by congr 1; ring
    _ ≤ |r * (α * d)| + |ψ * i * m| + |ψ * i * (α * d)| :=
      by linarith only [abs_add_le (r * (α * d) + ψ * i * m) (ψ * i * (α * d)),
        abs_add_le (r * (α * d)) (ψ * i * m)]
    _ ≤ _ := by linarith only [h₁, h₂, h₃]

private lemma abs_curvature_shift_product_error_le
    (r s i j ψ K : ℝ) (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1)
    (hK : 0 ≤ K) (hr : |r| ≤ K) (hs : |s| ≤ K)
    (hi : |i| ≤ 1) (hj : |j| ≤ 1) :
    |(r + ψ * i) * (s + ψ * j) - r * s| ≤ ψ * (2 * K + 1) := by
  have h := abs_mul_shift_error_le r s i j ψ ψ K K
    hψ hψ hψone hK hK hr hs hi hj
  nlinarith only [h]

lemma abs_curvature_twoTensor_replacement_le
    (R : I → I → I → I → ℝ) (M : I → I → ℝ) (W : I → ℝ)
    (α ψ KR KM : ℝ) (hα : 0 ≤ α) (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1)
    (hKR : 0 ≤ KR) (hKM : 0 ≤ KM)
    (hR : ∀ a b c d, |R a b c d| ≤ KR) (hM : ∀ a b, |M a b| ≤ KM) :
    |(∑ a, ∑ c, ∑ b, ∑ d,
        (R a c b d + ψ * twoFormIdentity a c b d) *
          (M c d + α * (if c = d then 1 else 0)) * W a * W b) -
      (∑ a, ∑ c, ∑ b, ∑ d, R a c b d * M c d * W a * W b)| ≤
      (Fintype.card I : ℝ) ^ 3 * ((KR + 1) * α + KM * ψ) * ∑ a, (W a) ^ 2 := by
  let C := (KR + 1) * α + KM * ψ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hentry (a c b d : I) :
      |((R a c b d + ψ * twoFormIdentity a c b d) *
          (M c d + α * (if c = d then 1 else 0)) - R a c b d * M c d) * W a * W b| ≤
        C / 2 * ((W a) ^ 2 + (W b) ^ 2) := by
    apply abs_mul_pair_le _ _ _ C hC
    exact abs_mul_shift_error_le _ _ _ _ α ψ KR KM hα hψ hψone hKR hKM
      (hR a c b d) (hM c d) (abs_twoFormIdentity_le_one a c b d)
      (by split_ifs <;> norm_num)
  calc
    _ = |∑ a, ∑ c, ∑ b, ∑ d,
      ((R a c b d + ψ * twoFormIdentity a c b d) *
        (M c d + α * (if c = d then 1 else 0)) - R a c b d * M c d) * W a * W b| := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ a, ∑ c, ∑ b, ∑ d,
      |((R a c b d + ψ * twoFormIdentity a c b d) *
        (M c d + α * (if c = d then 1 else 0)) - R a c b d * M c d) * W a * W b| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro c _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro b _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : I, ∑ c : I, ∑ b : I, ∑ d : I,
      C / 2 * ((W a) ^ 2 + (W b) ^ 2) := by
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun c _ =>
        Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun d _ => hentry a c b d))))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      dsimp only [C]
      ring

private lemma abs_mixed_shift_term_le
    (i p u w ψ K : ℝ) (hψ : 0 ≤ ψ) (hK : 0 ≤ K)
    (hi : |i| ≤ 1) (hp : |p| ≤ K) :
    |ψ * i * p * u * w| ≤ ψ / 2 * (u ^ 2 + K ^ 2 * w ^ 2) := by
  have h := abs_mul_pair_le i u (p * w) 1 (by norm_num) hi
  have hp₂ : p ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 hp
  have hpw := mul_le_mul_of_nonneg_right hp₂ (sq_nonneg w)
  have hbound : |i * u * (p * w)| ≤ (u ^ 2 + K ^ 2 * w ^ 2) / 2 := by
    nlinarith only [h, hpw]
  calc
    _ = ψ * |i * u * (p * w)| := by
      simp only [abs_mul, abs_of_nonneg hψ]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hbound hψ
      nlinarith only [hh]

lemma abs_curvature_threeTensor_replacement_le
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (U : I → I → ℝ) (W : I → ℝ) (ψ K : ℝ)
    (hψ : 0 ≤ ψ) (hK : 0 ≤ K) (hP : ∀ a b c, |P a b c| ≤ K) :
    |(∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        ((R a d b e + ψ * twoFormIdentity a d b e) * P d e c +
         (R a d c e + ψ * twoFormIdentity a d c e) * P d b e +
         (R b d c e + ψ * twoFormIdentity b d c e) * P a d e) * U a b * W c) -
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        (R a d b e * P d e c + R a d c e * P d b e + R b d c e * P a d e) * U a b * W c)| ≤
      3 / 2 * (Fintype.card I : ℝ) ^ 3 * ψ * (∑ a, ∑ b, (U a b) ^ 2) +
      3 / 2 * (Fintype.card I : ℝ) ^ 4 * ψ * K ^ 2 * ∑ a, (W a) ^ 2 := by
  let E := fun a b c d e =>
    (R a d b e + ψ * twoFormIdentity a d b e) * P d e c +
    (R a d c e + ψ * twoFormIdentity a d c e) * P d b e +
    (R b d c e + ψ * twoFormIdentity b d c e) * P a d e -
    (R a d b e * P d e c + R a d c e * P d b e + R b d c e * P a d e)
  have he (a b c d e : I) :
      |E a b c d e * U a b * W c| ≤ 3 * ψ / 2 * ((U a b) ^ 2 + K ^ 2 * (W c) ^ 2) := by
    have h₁ := abs_mixed_shift_term_le _ _ (U a b) (W c) ψ K hψ hK
      (abs_twoFormIdentity_le_one a d b e) (hP d e c)
    have h₂ := abs_mixed_shift_term_le _ _ (U a b) (W c) ψ K hψ hK
      (abs_twoFormIdentity_le_one a d c e) (hP d b e)
    have h₃ := abs_mixed_shift_term_le _ _ (U a b) (W c) ψ K hψ hK
      (abs_twoFormIdentity_le_one b d c e) (hP a d e)
    have hEq : E a b c d e * U a b * W c =
      ψ * twoFormIdentity a d b e * P d e c * U a b * W c +
      ψ * twoFormIdentity a d c e * P d b e * U a b * W c +
      ψ * twoFormIdentity b d c e * P a d e * U a b * W c := by dsimp [E]; ring
    rw [hEq]
    exact (abs_add_le _ _).trans (by
      have hh := abs_add_le
        (ψ * twoFormIdentity a d b e * P d e c * U a b * W c)
        (ψ * twoFormIdentity a d c e * P d b e * U a b * W c)
      nlinarith only [hh, h₁, h₂, h₃])
  calc
    _ = |∑ a, ∑ b, ∑ c, ∑ d, ∑ e, E a b c d e * U a b * W c| := by
      simp only [E, sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, |E a b c d e * U a b * W c| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro b _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro c _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro d _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : I, ∑ b : I, ∑ c : I, ∑ d : I, ∑ e : I,
        3 * ψ / 2 * ((U a b) ^ 2 + K ^ 2 * (W c) ^ 2) := by
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
        Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun d _ =>
          Finset.sum_le_sum (fun e _ => he a b c d e)))))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      ring

private lemma abs_curvatureB_replacement_le
    (R : I → I → I → I → ℝ) (ψ K : ℝ)
    (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1) (hK : 0 ≤ K)
    (hR : ∀ a b c d, |R a b c d| ≤ K) (a b c d : I) :
    |(∑ e, ∑ f, (R a e b f + ψ * twoFormIdentity a e b f) *
        (R c e d f + ψ * twoFormIdentity c e d f)) -
      (∑ e, ∑ f, R a e b f * R c e d f)| ≤
      (Fintype.card I : ℝ) ^ 2 * ψ * (2 * K + 1) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e, ∑ f, |(R a e b f + ψ * twoFormIdentity a e b f) *
        (R c e d f + ψ * twoFormIdentity c e d f) - R a e b f * R c e d f| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun e _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _e : I, ∑ _f : I, ψ * (2 * K + 1) := by
      exact Finset.sum_le_sum (fun e _ => Finset.sum_le_sum (fun f _ =>
        abs_curvature_shift_product_error_le _ _ _ _ ψ K hψ hψone hK
          (hR a e b f) (hR c e d f)
          (abs_twoFormIdentity_le_one a e b f) (abs_twoFormIdentity_le_one c e d f)))
    _ = _ := by simp; ring

lemma abs_curvature_reaction_replacement_le
    (R : I → I → I → I → ℝ) (U : I → I → ℝ) (ψ K : ℝ)
    (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1) (hK : 0 ≤ K)
    (hR : ∀ a b c d, |R a b c d| ≤ K) :
    let B := fun a b c d => ∑ e, ∑ f, R a e b f * R c e d f
    let Bhat := fun a b c d => ∑ e, ∑ f,
      (R a e b f + ψ * twoFormIdentity a e b f) *
        (R c e d f + ψ * twoFormIdentity c e d f)
    |(∑ a, ∑ b, ∑ c, ∑ d,
        (Bhat a b c d - Bhat a b d c - Bhat a d b c + Bhat a c b d) * U a b * U c d) -
      (∑ a, ∑ b, ∑ c, ∑ d,
        (B a b c d - B a b d c - B a d b c + B a c b d) * U a b * U c d)| ≤
      4 * (Fintype.card I : ℝ) ^ 4 * ψ * (2 * K + 1) * ∑ a, ∑ b, (U a b) ^ 2 := by
  dsimp only
  let B := fun a b c d => ∑ e, ∑ f, R a e b f * R c e d f
  let Bhat := fun a b c d => ∑ e, ∑ f,
    (R a e b f + ψ * twoFormIdentity a e b f) *
      (R c e d f + ψ * twoFormIdentity c e d f)
  let C := (Fintype.card I : ℝ) ^ 2 * ψ * (2 * K + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (a b c d : I) : |Bhat a b c d - B a b c d| ≤ C :=
    abs_curvatureB_replacement_le R ψ K hψ hψone hK hR a b c d
  have he (a b c d : I) :
      |(Bhat a b c d - Bhat a b d c - Bhat a d b c + Bhat a c b d) -
        (B a b c d - B a b d c - B a d b c + B a c b d)| ≤ 4 * C := by
    have h₁ := (abs_le.mp (hb a b c d))
    have h₂ := (abs_le.mp (hb a b d c))
    have h₃ := (abs_le.mp (hb a d b c))
    have h₄ := (abs_le.mp (hb a c b d))
    apply abs_le.mpr
    constructor <;> linarith only [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2, h₄.1, h₄.2]
  change |(∑ a, ∑ b, ∑ c, ∑ d,
    (Bhat a b c d - Bhat a b d c - Bhat a d b c + Bhat a c b d) * U a b * U c d) -
    (∑ a, ∑ b, ∑ c, ∑ d,
    (B a b c d - B a b d c - B a d b c + B a c b d) * U a b * U c d)| ≤ _
  calc
    _ = |∑ a, ∑ b, ∑ c, ∑ d,
      ((Bhat a b c d - Bhat a b d c - Bhat a d b c + Bhat a c b d) -
        (B a b c d - B a b d c - B a d b c + B a c b d)) * U a b * U c d| := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ d,
      |((Bhat a b c d - Bhat a b d c - Bhat a d b c + Bhat a c b d) -
        (B a b c d - B a b d c - B a d b c + B a c b d)) * U a b * U c d| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro b _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro c _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : I, ∑ b : I, ∑ c : I, ∑ d : I,
        (4 * C) / 2 * ((U a b) ^ 2 + (U c d) ^ 2) := by
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
        Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun d _ =>
          abs_mul_pair_le _ _ _ (4 * C) (by positivity) (he a b c d)))))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      dsimp only [C]
      ring

noncomputable def hamiltonCollectedReaction
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ) : ℝ :=
  let B := fun a b c d => ∑ e, ∑ f, R a e b f * R c e d f
  2 * (∑ a, ∑ c, ∑ b, ∑ d, R a c b d * M c d * W a * W b) -
    2 * (∑ a, ∑ c, ∑ d, ∑ b, P a c d * P b d c * W a * W b) +
    (∑ a, ∑ b, ∑ c, ∑ d, P c d a * P c d b * W a * W b) +
    4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
      (R a d b e * P d e c + R a d c e * P d b e + R b d c e * P a d e) *
        U a b * W c) +
    2 * (∑ a, ∑ b, ∑ c, ∑ d,
      (B a b c d - B a b d c - B a d b c + B a c b d) * U a b * U c d)

lemma abs_hamiltonCollectedReaction_replacement_le
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ)
    (α ψ KR KP KM : ℝ) (hα : 0 ≤ α) (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1)
    (hKR : 0 ≤ KR) (hKP : 0 ≤ KP) (hKM : 0 ≤ KM)
    (hR : ∀ a b c d, |R a b c d| ≤ KR)
    (hP : ∀ a b c, |P a b c| ≤ KP) (hM : ∀ a b, |M a b| ≤ KM) :
    |hamiltonCollectedReaction
        (fun a b c d => R a b c d + ψ * twoFormIdentity a b c d) P
        (fun a b => M a b + α * (if a = b then 1 else 0)) U W -
      hamiltonCollectedReaction R P M U W| ≤
      2 * (Fintype.card I : ℝ) ^ 3 * (KR + 1) * α * (∑ a, (W a) ^ 2) +
      (2 * (Fintype.card I : ℝ) ^ 3 * KM + 6 * (Fintype.card I : ℝ) ^ 4 * KP ^ 2) *
        ψ * (∑ a, (W a) ^ 2) +
      (6 * (Fintype.card I : ℝ) ^ 3 + 8 * (Fintype.card I : ℝ) ^ 4 * (2 * KR + 1)) *
        ψ * (∑ a, ∑ b, (U a b) ^ 2) := by
  have h₁ := abs_le.mp (abs_curvature_twoTensor_replacement_le R M W α ψ KR KM
    hα hψ hψone hKR hKM hR hM)
  have h₂ := abs_le.mp (abs_curvature_threeTensor_replacement_le R P U W ψ KP hψ hKP hP)
  have h₃ := abs_le.mp (abs_curvature_reaction_replacement_le R U ψ KR hψ hψone hKR hR)
  dsimp only [hamiltonCollectedReaction] at h₁ h₂ h₃ ⊢
  apply abs_le.mpr
  constructor <;> nlinarith only [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2]

lemma hamiltonCollectedReaction_ge_neg_replacement_error
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ)
    (α ψ KR KP KM : ℝ) (hα : 0 ≤ α) (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1)
    (hKR : 0 ≤ KR) (hKP : 0 ≤ KP) (hKM : 0 ≤ KM)
    (hR : ∀ a b c d, |R a b c d| ≤ KR)
    (hPb : ∀ a b c, |P a b c| ≤ KP) (hM : ∀ a b, |M a b| ≤ KM)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hbianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hP : ∀ a b c, P a b c = -P b a c)
    (hU : ∀ a b, U a b = -U b a)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2 +
        ψ * twoFormIdentity ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c)
      (fun a b => M a b + α * (if a = b then 1 else 0))).PosSemidef) :
    -(2 * (Fintype.card I : ℝ) ^ 3 * (KR + 1) * α * (∑ a, (W a) ^ 2) +
      (2 * (Fintype.card I : ℝ) ^ 3 * KM + 6 * (Fintype.card I : ℝ) ^ 4 * KP ^ 2) *
        ψ * (∑ a, (W a) ^ 2) +
      (6 * (Fintype.card I : ℝ) ^ 3 + 8 * (Fintype.card I : ℝ) ^ 4 * (2 * KR + 1)) *
        ψ * (∑ a, ∑ b, (U a b) ^ 2)) ≤ hamiltonCollectedReaction R P M U W := by
  have hnonneg : 0 ≤ hamiltonCollectedReaction
      (fun a b c d => R a b c d + ψ * twoFormIdentity a b c d) P
      (fun a b => M a b + α * (if a = b then 1 else 0)) U W := by
    apply hamilton_reaction_collected_nonneg _ _ _ _ _ _ _ _ _ hP hU hQ
    · intro a b c d
      rw [hfirst a b c d, twoFormIdentity_skew_first a b c d]
      ring
    · intro a b c d
      rw [hlast a b c d, twoFormIdentity_skew_last a b c d]
      ring
    · intro a b c d
      rw [hpair a b c d, twoFormIdentity_pair_swap a b c d]
    · intro a b c d
      have h₁ := hbianchi a b c d
      have h₂ := twoFormIdentity_bianchi a b c d
      have h₃ := congrArg (fun z : ℝ => ψ * z) h₂
      nlinarith only [h₁, h₃]
  have he := abs_le.mp (abs_hamiltonCollectedReaction_replacement_le
    R P M U W α ψ KR KP KM hα hψ hψone hKR hKP hKM hR hPb hM)
  linarith only [hnonneg, he.2]

lemma abs_hamiltonCollectedReaction_replacement_le_time_bound
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ)
    (α ψ K τ : ℝ) (hα : 0 ≤ α) (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1)
    (hK : 0 ≤ K) (hτ : 0 < τ)
    (hR : ∀ a b c d, |R a b c d| ≤ K)
    (hP : ∀ a b c, |P a b c| ≤ K * τ⁻¹)
    (hM : ∀ a b, |M a b| ≤ K * (1 + τ⁻¹)) :
    |hamiltonCollectedReaction
        (fun a b c d => R a b c d + ψ * twoFormIdentity a b c d) P
        (fun a b => M a b + α * (if a = b then 1 else 0)) U W -
      hamiltonCollectedReaction R P M U W| ≤
      2 * (Fintype.card I : ℝ) ^ 3 * (K + 1) * α * (∑ a, (W a) ^ 2) +
      (4 * (Fintype.card I : ℝ) ^ 3 * K + 6 * (Fintype.card I : ℝ) ^ 4 * K ^ 2) *
        ψ * (1 + (τ⁻¹) ^ 2) * (∑ a, (W a) ^ 2) +
      (6 * (Fintype.card I : ℝ) ^ 3 + 8 * (Fintype.card I : ℝ) ^ 4 * (2 * K + 1)) *
        ψ * (∑ a, ∑ b, (U a b) ^ 2) := by
  have he := abs_hamiltonCollectedReaction_replacement_le R P M U W
    α ψ K (K * τ⁻¹) (K * (1 + τ⁻¹)) hα hψ hψone hK
    (by positivity) (by positivity) hR hP hM
  have htime : 1 + τ⁻¹ ≤ 2 * (1 + (τ⁻¹) ^ 2) := by
    nlinarith only [sq_nonneg (τ⁻¹ - 1), sq_nonneg (τ⁻¹)]
  have hc₁ := mul_le_mul_of_nonneg_left htime
    (show 0 ≤ 2 * (Fintype.card I : ℝ) ^ 3 * K by positivity)
  have hc₂ :
      6 * (Fintype.card I : ℝ) ^ 4 * (K * τ⁻¹) ^ 2 ≤
        6 * (Fintype.card I : ℝ) ^ 4 * K ^ 2 * (1 + (τ⁻¹) ^ 2) := by
    nlinarith only [show 0 ≤ 6 * (Fintype.card I : ℝ) ^ 4 * K ^ 2 by positivity]
  have hc :
      2 * (Fintype.card I : ℝ) ^ 3 * (K * (1 + τ⁻¹)) +
        6 * (Fintype.card I : ℝ) ^ 4 * (K * τ⁻¹) ^ 2 ≤
      (4 * (Fintype.card I : ℝ) ^ 3 * K + 6 * (Fintype.card I : ℝ) ^ 4 * K ^ 2) *
        (1 + (τ⁻¹) ^ 2) := by nlinarith only [hc₁, hc₂]
  have hcw := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ ψ * (∑ a, (W a) ^ 2) by positivity)
  nlinarith only [he, hcw]

end Poincare.RicciFlow.Harnack
