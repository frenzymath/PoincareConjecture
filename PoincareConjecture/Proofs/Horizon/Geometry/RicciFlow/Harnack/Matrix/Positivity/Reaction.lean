import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith










set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace Poincare.RicciFlow.Harnack

variable {I : Type*} [Fintype I]



lemma tensorSquare_contraction_nonneg {A : Matrix I I ℝ}
    (hA : A.PosSemidef) (K : Matrix I I ℝ) :
    0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, K i k * (A i j * A k l) * K j l := by
  have h := (hA.kronecker hA).dotProduct_mulVec_nonneg
    (fun ik : I × I => K ik.1 ik.2)
  simpa only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Pi.star_apply,
    star_trivial, Matrix.kronecker_apply, Finset.mul_sum, mul_assoc] using h





lemma hamiltonSharpReaction_nonneg
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ)
    (hR : ∀ a b c d, R a b c d = R c d a b)
    (hP : ∀ a b c, P a b c = -P b a c)
    (hU : ∀ a b, U a b = -U b a)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef) :
    0 ≤ 2 * (∑ a, ∑ c, ∑ b, ∑ d, R a c b d * M c d * W a * W b) -
      2 * (∑ a, ∑ c, ∑ d, ∑ b, P a c d * P b d c * W a * W b) +
      8 * (∑ a, ∑ c, ∑ b, ∑ d, ∑ e, R a c d e * P c b e * U a b * W d) +
      4 * (∑ a, ∑ c, ∑ b, ∑ d, ∑ e, ∑ f,
        R a c d e * R b c f e * U a b * U d f) := by
  classical
  let A : Matrix ((I × I) ⊕ I) ((I × I) ⊕ I) ℝ := Matrix.fromBlocks
    (fun ac bd => R ac.1 ac.2 bd.1 bd.2) (fun ac d => P ac.1 ac.2 d)
    (fun c bd => P bd.1 bd.2 c) M
  let K : Matrix ((I × I) ⊕ I) ((I × I) ⊕ I) ℝ := Matrix.fromBlocks
    (fun ac bd => if ac.2 = bd.2 then -2 * U ac.1 bd.1 else 0)
    (fun ac d => if ac.2 = d then W ac.1 else 0)
    (fun c bd => if c = bd.2 then -W bd.1 else 0) 0
  have h := tensorSquare_contraction_nonneg (A := A) hQ K
  simp only [A, K, Fintype.sum_sum_type, Fintype.sum_prod_type] at h
  dsimp [Matrix.fromBlocks] at h
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_const_zero, add_zero, Finset.sum_ite_eq,
    Finset.sum_ite_irrel, Finset.mem_univ, if_true, ite_self] at h
  have h2 :
      (∑ a, ∑ c, ∑ b, ∑ d, ∑ e,
        -2 * U a b * (P a c d * R b c e d) * -W e) =
      (∑ a, ∑ c, ∑ b, ∑ d, ∑ e,
        -2 * U a b * (R a c d e * P b c e) * W d) := by
    let σ : (I × I × I × I × I) ≃ (I × I × I × I × I) :=
      { toFun := fun (a, c, b, d, e) => (b, c, a, e, d)
        invFun := fun (a, c, b, d, e) => (b, c, a, e, d)
        left_inv := by rintro ⟨a, c, b, d, e⟩; rfl
        right_inv := by rintro ⟨a, c, b, d, e⟩; rfl }
    have he := Fintype.sum_equiv σ
      (fun (a, c, b, d, e) => -2 * U a b * (P a c d * R b c e d) * -W e)
      (fun (a, c, b, d, e) => -2 * U a b * (R a c d e * P b c e) * W d)
      (by rintro ⟨a, c, b, d, e⟩; dsimp [σ]; rw [hU a b]; ring)
    simpa only [Fintype.sum_prod_type] using he
  have h3 :
      (∑ a, ∑ c, ∑ b, ∑ d, ∑ e,
        W a * (R a c b d * P e d c) * (-2 * U b e)) =
      (∑ a, ∑ c, ∑ b, ∑ d, ∑ e,
        -2 * U a b * (R a c d e * P b c e) * W d) := by
    let σ : (I × I × I × I × I) ≃ (I × I × I × I × I) :=
      { toFun := fun (a, c, b, d, e) => (b, d, e, a, c)
        invFun := fun (a, c, b, d, e) => (d, e, a, c, b)
        left_inv := by rintro ⟨a, c, b, d, e⟩; rfl
        right_inv := by rintro ⟨a, c, b, d, e⟩; rfl }
    have he := Fintype.sum_equiv σ
      (fun (a, c, b, d, e) => W a * (R a c b d * P e d c) * (-2 * U b e))
      (fun (a, c, b, d, e) => -2 * U a b * (R a c d e * P b c e) * W d)
      (by rintro ⟨a, c, b, d, e⟩; dsimp [σ]; rw [hR a c b d]; ring)
    simpa only [Fintype.sum_prod_type] using he
  have h4 :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        -W b * (P c d a * R b a e d) * (-2 * U c e)) =
      (∑ a, ∑ c, ∑ b, ∑ d, ∑ e,
        -2 * U a b * (R a c d e * P b c e) * W d) := by
    let σ : (I × I × I × I × I) ≃ (I × I × I × I × I) :=
      { toFun := fun (a, b, c, d, e) => (e, d, c, b, a)
        invFun := fun (a, b, c, d, e) => (e, d, c, b, a)
        left_inv := by rintro ⟨a, b, c, d, e⟩; rfl
        right_inv := by rintro ⟨a, b, c, d, e⟩; rfl }
    have he := Fintype.sum_equiv σ
      (fun (a, b, c, d, e) => -W b * (P c d a * R b a e d) * (-2 * U c e))
      (fun (a, c, b, d, e) => -2 * U a b * (R a c d e * P b c e) * W d)
      (by rintro ⟨a, b, c, d, e⟩; dsimp [σ]; rw [hR b a e d, hU c e]; ring)
    simpa only [Fintype.sum_prod_type] using he
  have hM :
      (∑ a, ∑ b, ∑ c, ∑ d, -W b * (M a c * R b a d c) * -W d) =
      (∑ a, ∑ c, ∑ b, ∑ d, W a * (R a c b d * M c d) * W b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hPP :
      (∑ a, ∑ b, ∑ c, ∑ d, -W b * (P c d a * P b a d) * W c) =
      (∑ a, ∑ c, ∑ d, ∑ b, W a * (P a c d * P b d c) * -W b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [h2, h3, h4, hM, hPP] at h
  have hquad (u v r s : ℝ) :
      -2 * u * (r * s) * (-2 * v) = 4 * (r * s * u * v) := by ring
  have hcross (a c b d e : I) :
      -2 * U a b * (R a c d e * P b c e) * W d =
        2 * (R a c d e * P c b e * U a b * W d) := by
    rw [hP b c e]
    ring
  have hlinear (a c b d : I) :
      W a * (R a c b d * M c d) * W b = R a c b d * M c d * W a * W b := by
    ring
  have hnegative (a c d b : I) :
      W a * (P a c d * P b d c) * -W b = -(P a c d * P b d c * W a * W b) := by
    ring
  simp_rw [hquad, hcross, hlinear, hnegative, ← Finset.mul_sum,
    Finset.sum_neg_distrib] at h
  linarith only [h]



lemma hamiltonReaction_nonneg
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ)
    (hR : ∀ a b c d, R a b c d = R c d a b)
    (hP : ∀ a b c, P a b c = -P b a c)
    (hU : ∀ a b, U a b = -U b a)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef) :
    0 ≤ 2 * (∑ a, ∑ c, ∑ b, ∑ d, R a c b d * M c d * W a * W b) -
      2 * (∑ a, ∑ c, ∑ d, ∑ b, P a c d * P b d c * W a * W b) +
      8 * (∑ a, ∑ c, ∑ b, ∑ d, ∑ e, R a c d e * P c b e * U a b * W d) +
      4 * (∑ a, ∑ c, ∑ b, ∑ d, ∑ e, ∑ f,
        R a c d e * R b c f e * U a b * U d f) +
      ∑ a, ∑ b, ((∑ c, P a b c * W c) + (∑ c, ∑ d, R a b c d * U c d)) ^ 2 := by
  exact add_nonneg (hamiltonSharpReaction_nonneg R P M U W hR hP hU hQ)
    (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)



lemma hamiltonBlock_quadratic_eq
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ) :
    let A := Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M
    let z : ((I × I) ⊕ I) → ℝ := Sum.elim (fun ac => U ac.1 ac.2) W
    z ⬝ᵥ (A *ᵥ z) =
      (∑ a, ∑ b, M a b * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d) := by
  dsimp only
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fintype.sum_prod_type]
  dsimp [Matrix.fromBlocks]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  have hcross : (∑ a, ∑ b, ∑ c, W a * (P b c a * U b c)) =
      ∑ a, ∑ b, ∑ c, U a b * (P a b c * W c) := by
    rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hcross]
  have hmul (u r v : ℝ) : u * (r * v) = r * u * v := by ring
  simp_rw [hmul]
  have htwo (p u w : ℝ) : p * u * 2 * w = 2 * (p * u * w) := by ring
  simp_rw [htwo, ← Finset.mul_sum]
  ring



lemma hamiltonBlock_posSemidef_iff
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ) (M : I → I → ℝ)
    (hR : ∀ a b c d, R a b c d = R c d a b)
    (hM : ∀ a b, M a b = M b a) :
    (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef ↔
    ∀ (U : I → I → ℝ) (W : I → ℝ),
      0 ≤ (∑ a, ∑ b, M a b * W a * W b) +
        2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
        (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d) := by
  let A := Matrix.fromBlocks
    (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
    (fun (ac : I × I) d => P ac.1 ac.2 d)
    (fun c (bd : I × I) => P bd.1 bd.2 c) M
  constructor
  · intro hQ U W
    have h := hQ.dotProduct_mulVec_nonneg (Sum.elim (fun ac : I × I => U ac.1 ac.2) W)
    simpa only [star_trivial, hamiltonBlock_quadratic_eq] using h
  · intro hQ
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · change A.conjTranspose = A
      ext (ac | a) (bd | b)
      · exact hR bd.1 bd.2 ac.1 ac.2
      · rfl
      · rfl
      · exact hM b a
    · intro z
      have hz : Sum.elim (fun ac : I × I => z (.inl ac)) (fun a => z (.inr a)) = z := by
        funext i
        cases i <;> rfl
      have h := hQ (fun a b => z (.inl (a, b))) (fun a => z (.inr a))
      rw [← hamiltonBlock_quadratic_eq] at h
      simpa only [star_trivial, hz] using h







lemma hamiltonBlock_quadratic_nonneg_of_posSemidef
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ) (M : I → I → ℝ)
    (hR : ∀ a b c d, R a b c d = R c d a b)
    (hM : ∀ a b, M a b = M b a)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef)
    (U : I → I → ℝ) (W : I → ℝ) :
    0 ≤ (∑ a, ∑ b, M a b * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d) := by
  exact (hamiltonBlock_posSemidef_iff R P M hR hM).mp hQ U W

private lemma skew_contraction_antisymmetrize (A U : I → I → ℝ)
    (hA : ∀ a b, A a b = -A b a) :
    (∑ a, ∑ b, A a b * ((U a b - U b a) / 2)) =
      ∑ a, ∑ b, A a b * U a b := by
  have hs : (∑ a, ∑ b, A a b * U b a) = -(∑ a, ∑ b, A a b * U a b) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hA b a]
    ring
  calc
    _ = ((∑ a, ∑ b, A a b * U a b) - (∑ a, ∑ b, A a b * U b a)) / 2 := by
      simp only [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [hs]; ring

private lemma sum_four_swap_pairs (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.sum_comm_cycle




lemma hamiltonBlock_antisymmetrize
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hP : ∀ a b c, P a b c = -P b a c) :
    let S := fun a b => (U a b - U b a) / 2
    (∑ a, ∑ b, M a b * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * S a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * S a b * S c d) =
    (∑ a, ∑ b, M a b * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d) := by
  dsimp only
  have hmixed (c : I) :
      (∑ a, ∑ b, P a b c * ((U a b - U b a) / 2) * W c) =
      ∑ a, ∑ b, P a b c * U a b * W c := by
    simpa only [Finset.sum_mul] using congrArg (fun z : ℝ => z * W c)
      (skew_contraction_antisymmetrize (fun a b => P a b c) U (fun a b => hP a b c))
  have hmix :
      (∑ a, ∑ b, ∑ c, P a b c * ((U a b - U b a) / 2) * W c) =
      ∑ a, ∑ b, ∑ c, P a b c * U a b * W c := by
    rw [Finset.sum_comm_cycle]
    simp_rw [hmixed]
    exact Finset.sum_comm_cycle.symm
  have hright (a b : I) :
      (∑ c, ∑ d, R a b c d * ((U a b - U b a) / 2) * ((U c d - U d c) / 2)) =
      ∑ c, ∑ d, R a b c d * ((U a b - U b a) / 2) * U c d := by
    apply skew_contraction_antisymmetrize
    intro c d
    rw [hlast a b c d]
    ring
  have hleft (c d : I) :
      (∑ a, ∑ b, R a b c d * ((U a b - U b a) / 2) * U c d) =
      ∑ a, ∑ b, R a b c d * U a b * U c d := by
    simpa only [Finset.sum_mul] using congrArg (fun z : ℝ => z * U c d)
      (skew_contraction_antisymmetrize (fun a b => R a b c d) U
        (fun a b => hfirst a b c d))
  rw [hmix]
  congr 1
  simp_rw [hright]
  rw [sum_four_swap_pairs]
  simp_rw [hleft]
  exact (sum_four_swap_pairs _).symm



lemma hamiltonBlock_posSemidef_of_skew_quadratic_nonneg
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ) (M : I → I → ℝ)
    (hR : ∀ a b c d, R a b c d = R c d a b)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hP : ∀ a b c, P a b c = -P b a c)
    (hM : ∀ a b, M a b = M b a)
    (hQ : ∀ (U : I → I → ℝ) (W : I → ℝ), (∀ a b, U a b = -U b a) →
      0 ≤ (∑ a, ∑ b, M a b * W a * W b) +
        2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
        (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d)) :
    (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef := by
  apply (hamiltonBlock_posSemidef_iff R P M hR hM).mpr
  intro U W
  have h := hQ (fun a b => (U a b - U b a) / 2) W (by intros; ring)
  rwa [hamiltonBlock_antisymmetrize R P M U W hfirst hlast hP] at h




lemma hamiltonBlock_null_equations
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef)
    (hnull : (∑ a, ∑ b, M a b * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d) = 0) :
    (∀ a b, (∑ c, P a b c * W c) + (∑ c, ∑ d, R a b c d * U c d) = 0) ∧
    (∀ a, (∑ c, ∑ d, P c d a * U c d) + (∑ b, M a b * W b) = 0) := by
  let A := Matrix.fromBlocks
    (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
    (fun (ac : I × I) d => P ac.1 ac.2 d)
    (fun c (bd : I × I) => P bd.1 bd.2 c) M
  let z : ((I × I) ⊕ I) → ℝ := Sum.elim (fun ac => U ac.1 ac.2) W
  have hz : A *ᵥ z = 0 := by
    apply hQ.dotProduct_mulVec_zero_iff z |>.mp
    simpa only [star_trivial, A, z, hamiltonBlock_quadratic_eq] using hnull
  constructor
  · intro a b
    have h := congrFun hz (.inl (a, b))
    simp only [A, z, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fintype.sum_prod_type] at h
    dsimp [Matrix.fromBlocks] at h
    exact (add_comm _ _).trans h
  · intro a
    have h := congrFun hz (.inr a)
    simp only [A, z, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fintype.sum_prod_type] at h
    exact h



lemma hamiltonBlock_vector_contraction_zero
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef)
    (hnull : (∑ a, ∑ b, M a b * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d) = 0) :
    (∑ a, ∑ b, M a b * W a * W b) +
      (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) = 0 := by
  have hz := (hamiltonBlock_null_equations R P M U W hQ hnull).2
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun a _ => congrArg (fun v : ℝ => v * W a) (hz a))
  have hcross : (∑ a, ∑ c, ∑ d, P c d a * U c d * W a) =
      ∑ a, ∑ b, ∑ c, P a b c * U a b * W c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  have hmul (a b) : M a b * W b * W a = M a b * W a * W b := by ring
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, zero_mul,
    Finset.sum_const_zero, hcross, hmul] at hs
  linarith only [hs]

end Poincare.RicciFlow.Harnack
