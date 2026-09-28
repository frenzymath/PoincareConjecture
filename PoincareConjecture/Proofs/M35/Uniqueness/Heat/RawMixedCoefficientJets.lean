import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCoefficientTimeJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.JetFamilyContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckDomainRegularityNative

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem contDiffOn_ordered_cutoffTimeJet_multiplier
    {a b : ℝ} (hab : a < b) (f : ℝ × X → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (A : ℝ → 𝓢(X, ℝ))
    (hA : ∀ t ∈ Icc a b, ∀ x, A t x = η x * f (t, x))
    (k : ℕ) (w : List (Fin n)) :
    ContDiffOn ℝ ∞ (fun t => schwartzMultiplier
      (orderedSchwartzDerivative w (cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k t)))
      (Icc a b) := by
  let B := cutoffTimeJet (uniqueDiffOn_Icc hab) f hf η hη A k
  have hB : ContDiffOn ℝ ∞ (fun p : ℝ × X => B p.1 p.2) (Icc a b ×ˢ univ) := by
    have he := (η.smooth'.comp_contDiffOn contDiffOn_snd).mul
      (contDiffOn_jointTimeJet (uniqueDiffOn_Icc hab) f hf k)
    apply he.congr
    intro p hp
    exact cutoffTimeJet_apply (uniqueDiffOn_Icc hab) f hf η hη A hA k hp.1 p.2
  have hsupport (t : ℝ) (ht : t ∈ Icc a b) : tsupport (B t) ⊆ tsupport η := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    apply subset_tsupport η
    intro hz
    exact hx (by rw [cutoffTimeJet_apply (uniqueDiffOn_Icc hab) f hf η hη A hA k ht, hz,
      zero_mul])
  exact contDiffOn_supported_ordered_multiplier hab B hB hη hsupport w

theorem contDiffOn_rawPrincipal_mixed_multiplier
    {J : Set ℝ} (F : RicciFlow n X J) {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ) (i j : Fin n) (w : List (Fin n)) :
    ContDiffOn ℝ ∞ (fun t => schwartzMultiplier
      (orderedSchwartzDerivative w (rawPrincipalTimeJet F hab hJ η hη k t i j)))
      (Icc a b) :=
  contDiffOn_ordered_cutoffTimeJet_multiplier hab _
    ((raw_inverseGram_entry_family_contDiffOn F i j).mono (prod_mono hJ Subset.rfl))
    η hη (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη i j)
    (fun _ _ _ => rfl) k w

theorem contDiffOn_rawFirst_mixed_multiplier
    {J : Set ℝ} (F : RicciFlow n X J) {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ) (i j l : Fin n)
    (w : List (Fin n)) :
    ContDiffOn ℝ ∞ (fun t => schwartzMultiplier
      (orderedSchwartzDerivative w (rawFirstTimeJet F hab hJ η hη k t i j l)))
      (Icc a b) :=
  contDiffOn_ordered_cutoffTimeJet_multiplier hab _
    ((rawFirstComponent_family_contDiffOn F i j l).mono (prod_mono hJ Subset.rfl))
    η hη (fun r => rawCutoffFirstComponent (F.connection r) η hη i j l)
    (fun _ _ _ => rfl) k w

theorem contDiffOn_rawZero_mixed_multiplier
    {J : Set ℝ} (F : RicciFlow n X J) {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (k : ℕ) (i j : Fin n) (w : List (Fin n)) :
    ContDiffOn ℝ ∞ (fun t => schwartzMultiplier
      (orderedSchwartzDerivative w (rawZeroTimeJet F hab hJ η hη k t i j)))
      (Icc a b) :=
  contDiffOn_ordered_cutoffTimeJet_multiplier hab _
    ((rawZeroComponent_family_contDiffOn F i j).mono (prod_mono hJ Subset.rfl))
    η hη (fun r => rawCutoffZeroComponent (F.connection r) η hη i j)
    (fun _ _ _ => rfl) k w

end PoincareConjecture.M35.Uniqueness.Heat
