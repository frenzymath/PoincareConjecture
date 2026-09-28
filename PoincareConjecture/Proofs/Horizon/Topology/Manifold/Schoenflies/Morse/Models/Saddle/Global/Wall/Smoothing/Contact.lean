import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Localization









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing


theorem rounding_zero_pos {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (hbound : ∀ s, |s| ≤ ρ s) : 0 < ρ 0 := by
  have hnonneg : 0 ≤ ρ 0 := by simpa using hbound 0
  by_contra hnot
  have heq : ρ 0 = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hd : deriv ρ 0 = 1 := deriv_eq_one_of_profileX_eq_zero hρ hbound
    (by simp [profileX, heq])
  have hmin : IsLocalMin (fun t => ρ t + t) 0 := by
    change ∀ᶠ t in 𝓝 (0 : Real), ρ 0 + 0 ≤ ρ t + t
    exact Eventually.of_forall (fun t => by
      rw [heq]
      linarith [hbound t, neg_abs_le t])
  have hz := hmin.hasDerivAt_eq_zero
    (((hρ.differentiable (by simp) 0).hasDerivAt).add (hasDerivAt_id 0))
  linarith

theorem profileX_zero_neg {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (hbound : ∀ s, |s| ≤ ρ s) : profileX ρ 0 < 0 := by
  unfold profileX
  linarith [rounding_zero_pos hρ hbound]

theorem profileHeight_eq_self_of_profileX_eq_zero {ρ : Real → Real}
    {s : Real} (hX : profileX ρ s = 0) : profileHeight ρ s = s := by
  have heq : ρ s = s := by
    unfold profileX at hX
    linarith
  rw [profileHeight, hX, profileW, heq]
  ring



theorem exists_profile_contact_threshold {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (hbound : ∀ s, |s| ≤ ρ s)
    (hLip : LipschitzWith 1 ρ) {δ : Real} (hδ : 0 < δ)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|) :
    ∃ a : Real, 0 < a ∧ a ≤ δ ∧
      ∀ s, profileX ρ s = 0 ↔ a ≤ s := by
  let K : Set Real := Icc 0 δ ∩ {s | profileX ρ s = 0}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_eq (contDiff_profileX hρ).continuous continuous_const)
  have hKne : K.Nonempty :=
    ⟨δ, ⟨hδ.le, le_rfl⟩, profileX_of_ge hδ htail le_rfl⟩
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne continuous_id.continuousOn
  have ha0 : 0 < a := lt_of_le_of_ne ha.1.1 (by
    intro heq
    have hazero : a = 0 := heq.symm
    exact (profileX_zero_neg hρ hbound).ne (hazero ▸ ha.2))
  refine ⟨a, ha0, ha.1.2, ?_⟩
  intro s
  constructor
  · intro hs
    by_cases hsδ : s ≤ δ
    · have hs0 : 0 ≤ s := by
        by_contra hsneg
        have hx := monotone_profileX hLip (le_of_lt (lt_of_not_ge hsneg))
        rw [hs] at hx
        exact (not_le_of_gt (profileX_zero_neg hρ hbound)) hx
      exact hmin ⟨⟨hs0, hsδ⟩, hs⟩
    · exact ha.1.2.trans (le_of_not_ge hsδ)
  · intro has
    apply le_antisymm (profileX_nonpos hbound s)
    have hmono := monotone_profileX hLip has
    have hazero : profileX ρ a = 0 := ha.2
    simpa only [hazero] using hmono



theorem exists_physical_contact_threshold (H : Real ≃ₘ[Real] Real)
    {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (hbound : ∀ s, |s| ≤ ρ s) (hLip : LipschitzWith 1 ρ)
    {δ : Real} (hδ : 0 < δ) (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hH : ∀ s, H s = profileHeight ρ s) (hmono : StrictMono H) :
    ∃ a : Real, 0 < a ∧ a ≤ δ ∧ H a = a ∧
      (∀ s, profileX ρ s = 0 ↔ a ≤ s) ∧
      ∀ q, profileX ρ (H.symm q) = 0 ↔ a ≤ q := by
  obtain ⟨a, ha0, haδ, hzero⟩ :=
    exists_profile_contact_threshold hρ hbound hLip hδ htail
  have hHa : H a = a := by
    rw [hH]
    exact profileHeight_eq_self_of_profileX_eq_zero ((hzero a).mpr le_rfl)
  refine ⟨a, ha0, haδ, hHa, hzero, ?_⟩
  intro q
  calc
    profileX ρ (H.symm q) = 0 ↔ a ≤ H.symm q := hzero _
    _ ↔ H a ≤ H (H.symm q) := hmono.le_iff_le.symm
    _ ↔ a ≤ q := by rw [hHa, H.apply_symm_apply]

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing
