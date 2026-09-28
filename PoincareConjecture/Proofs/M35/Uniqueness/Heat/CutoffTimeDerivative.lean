import PoincareConjecture.Proofs.M35.Uniqueness.Heat.MultiplierDerivative
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawTimeDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

def cutoffTimeDerivative {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (f : ℝ × X → ℝ) (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (t : ℝ) : 𝓢(X, ℝ) := by
  classical
  exact if ht : t ∈ J then
    EuclideanDerivativeNative.cutoffSchwartz η hη isOpen_univ (subset_univ _)
      (fun x => fderivWithin ℝ (fun s => f (s, x)) J t 1)
      ((raw_family_time_derivative_contDiffOn hJ hf).comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun x _ => ⟨ht, mem_univ x⟩))
    else 0

theorem cutoffTimeDerivative_apply {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (f : ℝ × X → ℝ) (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) {t : ℝ} (ht : t ∈ J) (x : X) :
    cutoffTimeDerivative hJ f hf η hη t x =
      η x * fderivWithin ℝ (fun s => f (s, x)) J t 1 := by
  simp only [cutoffTimeDerivative, dif_pos ht, EuclideanDerivativeNative.cutoffSchwartz_apply]

theorem cutoffTimeDerivative_joint_continuousOn {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (f : ℝ × X → ℝ) (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) :
    ContinuousOn (fun p : ℝ × X => cutoffTimeDerivative hJ f hf η hη p.1 p.2)
      (J ×ˢ univ) := by
  have hηc : ContinuousOn (fun p : ℝ × X => η p.2) (J ×ˢ univ) :=
    η.continuous.comp_continuousOn continuousOn_snd
  exact (hηc.mul (raw_family_time_derivative_contDiffOn hJ hf).continuousOn).congr
    (fun p hp => cutoffTimeDerivative_apply hJ f hf η hη hp.1 p.2)

theorem cutoffTimeDerivative_zero_of_notMem {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (f : ℝ × X → ℝ) (hf : ContDiffOn ℝ ∞ f (J ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) {t : ℝ} (ht : t ∈ J)
    {x : X} (hx : x ∉ tsupport η) : cutoffTimeDerivative hJ f hf η hη t x = 0 := by
  rw [cutoffTimeDerivative_apply hJ f hf η hη ht, image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem hasDerivWithinAt_actual_cutoff_multiplier
    {a b : ℝ} (hab : a < b) (f : ℝ × X → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x))
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => EuclideanDerivativeNative.schwartzMultiplier (A s))
      (EuclideanDerivativeNative.schwartzMultiplier
        (cutoffTimeDerivative (uniqueDiffOn_Icc hab) f hf η hη t)) (Icc a b) t := by
  let hJ := uniqueDiffOn_Icc hab
  let d := cutoffTimeDerivative hJ f hf η hη
  apply hasDerivWithinAt_schwartzMultiplier hη A d ?_ ?_ ?_ ?_ ht
  · intro s hs x
    rw [cutoffTimeDerivative_apply hJ f hf η hη hs]
    exact ((raw_family_time_hasDerivWithinAt hf hs x).const_mul (η x)).congr_of_mem
      (fun r hr => hA r hr x) hs
  · exact (cutoffTimeDerivative_joint_continuousOn hJ f hf η hη).mono
      (prod_mono Subset.rfl (subset_univ _))
  · intro s hs x hx
    rw [hA s hs x, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · intro s hs x hx
    exact cutoffTimeDerivative_zero_of_notMem hJ f hf η hη hs hx

theorem hasDerivWithinAt_actual_cutoff_value_multiplier (K : Set X)
    {a b : ℝ} (hab : a < b) (f : ℝ × X → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x))
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => dirichletValueMultiplier K (A s))
      (dirichletValueMultiplier K
        (cutoffTimeDerivative (uniqueDiffOn_Icc hab) f hf η hη t)) (Icc a b) t := by
  let hJ := uniqueDiffOn_Icc hab
  let d := cutoffTimeDerivative hJ f hf η hη
  apply hasDerivWithinAt_dirichletValueMultiplier K hη A d ?_ ?_ ?_ ?_ ht
  · intro s hs x
    rw [cutoffTimeDerivative_apply hJ f hf η hη hs]
    exact ((raw_family_time_hasDerivWithinAt hf hs x).const_mul (η x)).congr_of_mem
      (fun r hr => hA r hr x) hs
  · exact (cutoffTimeDerivative_joint_continuousOn hJ f hf η hη).mono
      (prod_mono Subset.rfl (subset_univ _))
  · intro s hs x hx
    rw [hA s hs x, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · intro s hs x hx
    exact cutoffTimeDerivative_zero_of_notMem hJ f hf η hη hs hx

end PoincareConjecture.M35.Uniqueness.Heat
