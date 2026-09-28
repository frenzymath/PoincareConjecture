import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CutoffTimeDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem hasDerivWithinAt_actual_cutoff_operator
    (L : 𝓢(X, ℝ) →ₗ[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ f : 𝓢(X, ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ x, ‖f x‖ ≤ M) → ‖L f‖ ≤ C * M)
    {a b : ℝ} (hab : a < b) (f : ℝ × X → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x))
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => L (A s))
      (L (cutoffTimeDerivative (uniqueDiffOn_Icc hab) f hf η hη t)) (Icc a b) t := by
  let hJ := uniqueDiffOn_Icc hab
  let d := cutoffTimeDerivative hJ f hf η hη
  apply hasDerivWithinAt_coefficientOperator (L.comp (LinearMap.proj ())) hC
    (fun A M hM hA => hL (A ()) M hM (hA ())) hη
    (fun s _ => A s) (fun s _ => d s) ?_ ?_ ?_ ?_ ht
  · intro s hs _ x
    rw [cutoffTimeDerivative_apply hJ f hf η hη hs]
    exact ((raw_family_time_hasDerivWithinAt hf hs x).const_mul (η x)).congr_of_mem
      (fun r hr => hA r hr x) hs
  · apply continuousOn_pi.mpr
    intro _
    exact (cutoffTimeDerivative_joint_continuousOn hJ f hf η hη).mono
      (prod_mono Subset.rfl (subset_univ _))
  · intro s hs _ x hx
    rw [hA s hs x, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · intro s hs _ x hx
    exact cutoffTimeDerivative_zero_of_notMem hJ f hf η hη hs hx

theorem contDiffOn_actual_cutoff_operator_nat
    (L : 𝓢(X, ℝ) →ₗ[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ f : 𝓢(X, ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ x, ‖f x‖ ≤ M) → ‖L f‖ ≤ C * M)
    {a b : ℝ} (hab : a < b) (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ)
    (f : ℝ × X → ℝ) (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (A : ℝ → 𝓢(X, ℝ)) (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x)) :
    ContDiffOn ℝ k (fun t => L (A t)) (Icc a b) := by
  induction k generalizing f A with
  | zero =>
    apply contDiffOn_zero.mpr
    intro t ht
    exact (hasDerivWithinAt_actual_cutoff_operator L hC hL hab f hf η hη A hA ht).continuousWithinAt
  | succ k ih =>
    let hJ := uniqueDiffOn_Icc hab
    let f' : ℝ × X → ℝ := fun p =>
      fderivWithin ℝ (fun s => f (s, p.2)) (Icc a b) p.1 1
    have hf' : ContDiffOn ℝ ∞ f' (Icc a b ×ˢ univ) :=
      raw_family_time_derivative_contDiffOn hJ hf
    let D := cutoffTimeDerivative hJ f hf η hη
    have hD : ContDiffOn ℝ k (fun t => L (D t)) (Icc a b) :=
      ih f' hf' D (fun t ht x => cutoffTimeDerivative_apply hJ f hf η hη ht x)
    have hd (t : ℝ) (ht : t ∈ Icc a b) :
        HasDerivWithinAt (fun s => L (A s)) (L (D t)) (Icc a b) t :=
      hasDerivWithinAt_actual_cutoff_operator L hC hL hab f hf η hη A hA ht
    rw [show (↑(k + 1) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_derivWithin hJ]
    refine ⟨fun t ht => (hd t ht).differentiableWithinAt, ?_, ?_⟩
    · simp
    · exact hD.congr (fun t ht => (hd t ht).derivWithin (hJ t ht))

theorem contDiffOn_actual_cutoff_operator
    (L : 𝓢(X, ℝ) →ₗ[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ f : 𝓢(X, ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ x, ‖f x‖ ≤ M) → ‖L f‖ ≤ C * M)
    {a b : ℝ} (hab : a < b) (f : ℝ × X → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x)) :
    ContDiffOn ℝ ∞ (fun t => L (A t)) (Icc a b) := by
  apply contDiffOn_infty.mpr
  intro k
  exact contDiffOn_actual_cutoff_operator_nat L hC hL hab η hη k f hf A hA

end PoincareConjecture.M35.Uniqueness.Heat
