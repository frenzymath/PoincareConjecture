import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CutoffOperatorSmooth









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

def jointTimeJet (J : Set ℝ) (f : ℝ × X → ℝ) : ℕ → ℝ × X → ℝ
  | 0 => f
  | k + 1 => fun p => fderivWithin ℝ (fun s => jointTimeJet J f k (s, p.2)) J p.1 1

theorem contDiffOn_jointTimeJet {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (f : ℝ × X → ℝ) (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ)) (k : ℕ) :
    ContDiffOn ℝ ∞ (jointTimeJet J f k) (J ×ˢ univ) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact raw_family_time_derivative_contDiffOn hJ ih

def cutoffTimeJet {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (f : ℝ × X → ℝ) (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ)) : ℕ → ℝ → 𝓢(X, ℝ)
  | 0 => A
  | k + 1 => cutoffTimeDerivative hJ (jointTimeJet J f k)
      (contDiffOn_jointTimeJet hJ f hf k) η hη

theorem cutoffTimeJet_apply {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (f : ℝ × X → ℝ) (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ J, ∀ x, A t x = η x * f (t, x))
    (k : ℕ) {t : ℝ} (ht : t ∈ J) (x : X) :
    cutoffTimeJet hJ f hf η hη A k t x = η x * jointTimeJet J f k (t, x) := by
  cases k with
  | zero => exact hA t ht x
  | succ k =>
    exact cutoffTimeDerivative_apply hJ (jointTimeJet J f k)
      (contDiffOn_jointTimeJet hJ f hf k) η hη ht x

theorem hasDerivWithinAt_cutoffTimeJet_operator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : 𝓢(X, ℝ) →ₗ[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : 𝓢(X, ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ x, ‖g x‖ ≤ M) → ‖L g‖ ≤ C * M)
    {a b : ℝ} (hab : a < b) (f : ℝ × X → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x))
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => L (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k s))
      (L (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A (k + 1) t)) (Icc a b) t := by
  apply hasDerivWithinAt_actual_cutoff_operator L hC hL hab (jointTimeJet (Icc a b) f k)
    (contDiffOn_jointTimeJet (uniqueDiffOn_Icc hab) f hf k) η hη
    (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k)
    (fun s hs x => cutoffTimeJet_apply (uniqueDiffOn_Icc hab) f hf η hη A hA k hs x) ht

theorem contDiffOn_cutoffTimeJet_operator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : 𝓢(X, ℝ) →ₗ[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ g : 𝓢(X, ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ x, ‖g x‖ ≤ M) → ‖L g‖ ≤ C * M)
    {a b : ℝ} (hab : a < b) (f : ℝ × X → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun t => L (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k t))
      (Icc a b) :=
  contDiffOn_actual_cutoff_operator L hC hL hab (jointTimeJet (Icc a b) f k)
    (contDiffOn_jointTimeJet (uniqueDiffOn_Icc hab) f hf k) η hη
    (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k)
    (fun _t ht x => cutoffTimeJet_apply (uniqueDiffOn_Icc hab) f hf η hη A hA k ht x)

theorem hasDerivWithinAt_cutoffTimeJet_multiplier
    {a b : ℝ} (hab : a < b) (f : ℝ × X → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x))
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => EuclideanDerivativeNative.schwartzMultiplier
      (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k s))
      (EuclideanDerivativeNative.schwartzMultiplier
        (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A (k + 1) t)) (Icc a b) t :=
  hasDerivWithinAt_actual_cutoff_multiplier hab (jointTimeJet (Icc a b) f k)
    (contDiffOn_jointTimeJet (uniqueDiffOn_Icc hab) f hf k) η hη
    (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k)
    (fun _s hs x => cutoffTimeJet_apply (uniqueDiffOn_Icc hab) f hf η hη A hA k hs x) ht

theorem hasDerivWithinAt_cutoffTimeJet_value_multiplier (K : Set X)
    {a b : ℝ} (hab : a < b) (f : ℝ × X → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x))
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => dirichletValueMultiplier K
      (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k s))
      (dirichletValueMultiplier K
        (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A (k + 1) t)) (Icc a b) t :=
  hasDerivWithinAt_actual_cutoff_value_multiplier K hab (jointTimeJet (Icc a b) f k)
    (contDiffOn_jointTimeJet (uniqueDiffOn_Icc hab) f hf k) η hη
    (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k)
    (fun _s hs x => cutoffTimeJet_apply (uniqueDiffOn_Icc hab) f hf η hη A hA k hs x) ht

end PoincareConjecture.M35.Uniqueness.Heat
