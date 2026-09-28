import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Reaction

set_option autoImplicit false

open scoped BigOperators

namespace Poincare.RicciFlow.Harnack

variable {I : Type*} [Fintype I]

lemma curvature_bianchi_skew_contraction
    (R : I → I → I → I → ℝ) (P : I → I → ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hbianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hP : ∀ a b, P a b = -P b a) (a b : I) :
    2 * (∑ d, ∑ e, R a d b e * P d e) =
      ∑ d, ∑ e, R a b d e * P d e := by
  have hpoint (d e : I) : R a b d e = R a d b e - R a e b d := by
    have h := hbianchi a d b e
    rw [hpair d b a e, hlast a e d b, hfirst b a d e] at h
    linarith only [h]
  have hswap : (∑ d, ∑ e, R a e b d * P d e) =
      -(∑ d, ∑ e, R a d b e * P d e) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    rw [hP e d]
    ring
  simp only [hpoint, sub_mul, Finset.sum_sub_distrib, hswap]
  ring

lemma hamiltonP_reaction_quadratic_contraction
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (U : I → I → ℝ) (W : I → ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hbianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hP : ∀ a b c, P a b c = -P b a c)
    (hU : ∀ a b, U a b = -U b a) :
    4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
      (R a d b e * P d e c + R a d c e * P d b e + R b d c e * P a d e) *
        U a b * W c) =
      8 * (∑ a, ∑ d, ∑ b, ∑ c, ∑ e, R a d c e * P d b e * U a b * W c) +
      2 * (∑ a, ∑ b, (∑ c, P a b c * W c) * (∑ d, ∑ e, R a b d e * U d e)) := by
  have hswap :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, R b d c e * P a d e * U a b * W c) =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, R a d c e * P d b e * U a b * W c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    rw [hP b d e, hU b a]
    ring
  have hcross :
      2 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, R a d b e * P d e c * U a b * W c) =
        ∑ a, ∑ b, (∑ c, P a b c * W c) * (∑ d, ∑ e, R a b d e * U d e) := by
    have hlocal (a b c : I) :
        2 * (∑ d, ∑ e, R a d b e * P d e c * U a b * W c) =
          ∑ d, ∑ e, R a b d e * P d e c * U a b * W c := by
      simpa only [Finset.sum_mul, mul_assoc] using congrArg
        (fun q : ℝ => q * U a b * W c)
        (curvature_bianchi_skew_contraction R (fun d e => P d e c)
          hfirst hlast hpair hbianchi (fun d e => hP d e c) a b)
    have hsum := congrArg
      (fun f : I → I → I → ℝ => ∑ a, ∑ b, ∑ c, f a b c)
      (funext fun a => funext fun b => funext (hlocal a b))
    simp only [← Finset.mul_sum] at hsum
    rw [hsum]
    let σ : (I × I × I × I × I) ≃ (I × I × I × I × I) :=
      { toFun := fun (a, b, c, d, e) => (d, e, c, a, b)
        invFun := fun (a, b, c, d, e) => (d, e, c, a, b)
        left_inv := by rintro ⟨a, b, c, d, e⟩; rfl
        right_inv := by rintro ⟨a, b, c, d, e⟩; rfl }
    have he := Fintype.sum_equiv σ
      (fun (a, b, c, d, e) => R a b d e * P d e c * U a b * W c)
      (fun (a, b, c, d, e) => P a b c * W c * (R a b d e * U d e))
      (by rintro ⟨a, b, c, d, e⟩; dsimp [σ]; rw [hpair a b d e]; ring)
    simp only [Fintype.sum_prod_type] at he
    rw [he]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have horder :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, R a d c e * P d b e * U a b * W c) =
        ∑ a, ∑ d, ∑ b, ∑ c, ∑ e, R a d c e * P d b e * U a b * W c := by
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm_cycle
  simp only [add_mul, Finset.sum_add_distrib, hswap]
  rw [← horder]
  linarith only [hcross]

lemma curvatureB_quadratic_eq_square
    (R : I → I → I → I → ℝ) (U : I → I → ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hbianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hU : ∀ a b, U a b = -U b a) :
    4 * (∑ a, ∑ b, ∑ c, ∑ d,
      (∑ e, ∑ f, R a e b f * R c e d f) * U a b * U c d) =
        ∑ e, ∑ f, (∑ a, ∑ b, R e f a b * U a b) ^ 2 := by
  classical
  have hflip (a e b f : I) : R a e b f = R e a f b := by
    rw [hfirst a e b f, hlast e a b f, neg_neg]
  have hlocal (e f : I) :
      2 * (∑ a, ∑ b, R a e b f * U a b) = ∑ a, ∑ b, R e f a b * U a b := by
    simpa only [hflip] using
      curvature_bianchi_skew_contraction R U hfirst hlast hpair hbianchi hU e f
  have horder :
      (∑ a, ∑ b, ∑ c, ∑ d, (∑ e, ∑ f, R a e b f * R c e d f) * U a b * U c d) =
        ∑ e, ∑ f, (∑ a, ∑ b, R a e b f * U a b) ^ 2 := by
    let σ : (I × I × I × I × I × I) ≃ (I × I × I × I × I × I) :=
      { toFun := fun (a, b, c, d, e, f) => (e, f, a, b, c, d)
        invFun := fun (e, f, a, b, c, d) => (a, b, c, d, e, f)
        left_inv := by rintro ⟨a, b, c, d, e, f⟩; rfl
        right_inv := by rintro ⟨e, f, a, b, c, d⟩; rfl }
    have he := Fintype.sum_equiv σ
      (fun (a, b, c, d, e, f) => (R a e b f * R c e d f) * U a b * U c d)
      (fun (e, f, a, b, c, d) => (R a e b f * U a b) * (R c e d f * U c d))
      (by rintro ⟨a, b, c, d, e, f⟩; dsimp [σ]; ring)
    simp only [Fintype.sum_prod_type] at he
    simp only [Finset.sum_mul]
    rw [he]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  rw [horder, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [← hlocal]
  ring

lemma curvature_reaction_quadratic_contraction
    (R : I → I → I → I → ℝ) (U : I → I → ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hbianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hU : ∀ a b, U a b = -U b a) :
    let B := fun a b c d => ∑ e, ∑ f, R a e b f * R c e d f
    2 * (∑ a, ∑ b, ∑ c, ∑ d,
      (B a b c d - B a b d c - B a d b c + B a c b d) * U a b * U c d) =
      4 * (∑ a, ∑ e, ∑ b, ∑ c, ∑ f, ∑ d, R a e c f * R b e d f * U a b * U c d) +
      ∑ a, ∑ b, (∑ c, ∑ d, R a b c d * U c d) ^ 2 := by
  let B := fun a b c d => ∑ e, ∑ f, R a e b f * R c e d f
  have hswap (A : I → I → I → I → ℝ) :
      (∑ a, ∑ b, ∑ c, ∑ d, A a b d c * U a b * U c d) =
        -(∑ a, ∑ b, ∑ c, ∑ d, A a b c d * U a b * U c d) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [hU d c]
    ring
  have hs₁ := hswap B
  have hs₂ := hswap (fun a b c d => B a c b d)
  have hsquare := curvatureB_quadratic_eq_square R U hfirst hlast hpair hbianchi hU
  have horder : (∑ a, ∑ b, ∑ c, ∑ d, B a c b d * U a b * U c d) =
      ∑ a, ∑ e, ∑ b, ∑ c, ∑ f, ∑ d, R a e c f * R b e d f * U a b * U c d := by
    classical
    let σ : (I × I × I × I × I × I) ≃ (I × I × I × I × I × I) :=
      { toFun := fun (a, b, c, d, e, f) => (a, e, b, c, f, d)
        invFun := fun (a, e, b, c, f, d) => (a, b, c, d, e, f)
        left_inv := by rintro ⟨a, b, c, d, e, f⟩; rfl
        right_inv := by rintro ⟨a, e, b, c, f, d⟩; rfl }
    have he := Fintype.sum_equiv σ
      (fun (a, b, c, d, e, f) => (R a e c f * R b e d f) * U a b * U c d)
      (fun (a, e, b, c, f, d) => R a e c f * R b e d f * U a b * U c d)
      (by rintro ⟨a, b, c, d, e, f⟩; rfl)
    simpa only [B, Finset.sum_mul, Fintype.sum_prod_type] using he
  dsimp only
  change 2 * (∑ a, ∑ b, ∑ c, ∑ d,
    (B a b c d - B a b d c - B a d b c + B a c b d) * U a b * U c d) = _
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hs₁, hs₂, horder]
  dsimp only [B]
  linarith only [hsquare]

lemma hamilton_reaction_collected_nonneg
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hbianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hP : ∀ a b c, P a b c = -P b a c)
    (hU : ∀ a b, U a b = -U b a)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef) :
    let B := fun a b c d => ∑ e, ∑ f, R a e b f * R c e d f
    0 ≤ 2 * (∑ a, ∑ c, ∑ b, ∑ d, R a c b d * M c d * W a * W b) -
      2 * (∑ a, ∑ c, ∑ d, ∑ b, P a c d * P b d c * W a * W b) +
      (∑ a, ∑ b, ∑ c, ∑ d, P c d a * P c d b * W a * W b) +
      4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        (R a d b e * P d e c + R a d c e * P d b e + R b d c e * P a d e) *
          U a b * W c) +
      2 * (∑ a, ∑ b, ∑ c, ∑ d,
        (B a b c d - B a b d c - B a d b c + B a c b d) * U a b * U c d) := by
  have hp := hamiltonP_reaction_quadratic_contraction R P U W
    hfirst hlast hpair hbianchi hP hU
  have hr := curvature_reaction_quadratic_contraction R U
    hfirst hlast hpair hbianchi hU
  have hnonneg := hamiltonReaction_nonneg R P M U W hpair hP hU hQ
  have hPP : (∑ a, ∑ b, ∑ c, ∑ d, P c d a * P c d b * W a * W b) =
      ∑ c, ∑ d, (∑ a, P c d a * W a) ^ 2 := by
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro d _
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hsquare :
      (∑ a, ∑ b, ((∑ c, P a b c * W c) + (∑ c, ∑ d, R a b c d * U c d)) ^ 2) =
      (∑ a, ∑ b, (∑ c, P a b c * W c) ^ 2) +
      2 * (∑ a, ∑ b, (∑ c, P a b c * W c) * (∑ c, ∑ d, R a b c d * U c d)) +
      (∑ a, ∑ b, (∑ c, ∑ d, R a b c d * U c d) ^ 2) := by
    simp only [add_sq, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  dsimp only at hr ⊢
  rw [hp, hr, hPP]
  rw [hsquare] at hnonneg
  linarith only [hnonneg]

end Poincare.RicciFlow.Harnack
