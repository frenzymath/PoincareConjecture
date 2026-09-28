import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.SmoothAbsolute
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.ParametricInverse
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing

def profileX (ρ : Real → Real) (s : Real) : Real := (s - ρ s) / 2

def profileW (ρ : Real → Real) (s : Real) : Real := (s + ρ s) / 2

def profileHeight (ρ : Real → Real) (s : Real) : Real :=
  profileW ρ s - (profileX ρ s)^2

theorem profileX_nonpos {ρ : Real → Real} (hρ : ∀ s, |s| ≤ ρ s) (s : Real) :
    profileX ρ s ≤ 0 := by
  unfold profileX
  linarith [le_abs_self s, hρ s]

theorem profileW_nonneg {ρ : Real → Real} (hρ : ∀ s, |s| ≤ ρ s) (s : Real) :
    0 ≤ profileW ρ s := by
  unfold profileW
  linarith [neg_abs_le s, hρ s]

theorem contDiff_profileX {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ) :
    ContDiff Real ∞ (profileX ρ) :=
  (contDiff_id.sub hρ).div_const 2

theorem contDiff_profileW {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ) :
    ContDiff Real ∞ (profileW ρ) :=
  (contDiff_id.add hρ).div_const 2

theorem contDiff_profileHeight {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ) :
    ContDiff Real ∞ (profileHeight ρ) :=
  (contDiff_profileW hρ).sub ((contDiff_profileX hρ).pow 2)

theorem hasDerivAt_profileHeight {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (s : Real) :
    HasDerivAt (profileHeight ρ)
      ((1 + deriv ρ s) / 2 - 2 * profileX ρ s * ((1 - deriv ρ s) / 2)) s := by
  have hd := (hρ.differentiable (by simp) s).hasDerivAt
  have hX : HasDerivAt (profileX ρ) ((1 - deriv ρ s) / 2) s :=
    ((hasDerivAt_id s).sub hd).div_const 2
  have hW : HasDerivAt (profileW ρ) ((1 + deriv ρ s) / 2) s :=
    ((hasDerivAt_id s).add hd).div_const 2
  convert hW.sub (hX.pow 2) using 1 <;> first | rfl | norm_num

theorem deriv_eq_one_of_profileX_eq_zero {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (hlower : ∀ s, |s| ≤ ρ s)
    {s : Real} (hX : profileX ρ s = 0) : deriv ρ s = 1 := by
  have heq : ρ s = s := by
    unfold profileX at hX
    linarith
  have hmin : IsLocalMin (fun t => ρ t - t) s := by
    change ∀ᶠ t in 𝓝 s, ρ s - s ≤ ρ t - t
    exact Eventually.of_forall (fun t => by rw [heq]; linarith [hlower t, le_abs_self t])
  have hd := hmin.hasDerivAt_eq_zero
    (((hρ.differentiable (by simp) s).hasDerivAt).sub (hasDerivAt_id s))
  linarith

theorem deriv_profileHeight_pos {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (hlower : ∀ s, |s| ≤ ρ s)
    (hderiv : ∀ s, |deriv ρ s| ≤ 1) (s : Real) :
    0 < deriv (profileHeight ρ) s := by
  rw [(hasDerivAt_profileHeight hρ s).deriv]
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp (hderiv s)
  by_cases hd : deriv ρ s = 1
  · simp [hd]
  have hX : profileX ρ s < 0 := lt_of_le_of_ne (profileX_nonpos hlower s)
    (fun hzero => hd (deriv_eq_one_of_profileX_eq_zero hρ hlower hzero))
  have hp : 0 < (-profileX ρ s) * (1 - deriv ρ s) :=
    mul_pos (neg_pos.mpr hX) (sub_pos.mpr (lt_of_le_of_ne hdhi hd))
  nlinarith

theorem strictMono_profileHeight {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (hlower : ∀ s, |s| ≤ ρ s)
    (hderiv : ∀ s, |deriv ρ s| ≤ 1) : StrictMono (profileHeight ρ) :=
  strictMono_of_deriv_pos (deriv_profileHeight_pos hρ hlower hderiv)

theorem profileX_of_le {ρ : Real → Real} {δ s : Real} (hδ : 0 < δ)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|) (hs : s ≤ -δ) :
    profileX ρ s = s := by
  have hs0 : s ≤ 0 := by linarith
  rw [profileX, htail s (by rw [abs_of_nonpos hs0]; linarith), abs_of_nonpos hs0]
  ring

theorem profileX_of_ge {ρ : Real → Real} {δ s : Real} (hδ : 0 < δ)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|) (hs : δ ≤ s) :
    profileX ρ s = 0 := by
  rw [profileX, htail s (by rw [abs_of_nonneg (hδ.le.trans hs)]; exact hs),
    abs_of_nonneg (hδ.le.trans hs)]
  ring

theorem profileHeight_of_le {ρ : Real → Real} {δ s : Real} (hδ : 0 < δ)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|) (hs : s ≤ -δ) :
    profileHeight ρ s = -s^2 := by
  have hs0 : s ≤ 0 := by linarith
  rw [profileHeight, profileX_of_le hδ htail hs, profileW,
    htail s (by rw [abs_of_nonpos hs0]; linarith), abs_of_nonpos hs0]
  ring

theorem profileHeight_of_ge {ρ : Real → Real} {δ s : Real} (hδ : 0 < δ)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|) (hs : δ ≤ s) :
    profileHeight ρ s = s := by
  rw [profileHeight, profileX_of_ge hδ htail hs, profileW,
    htail s (by rw [abs_of_nonneg (hδ.le.trans hs)]; exact hs),
    abs_of_nonneg (hδ.le.trans hs)]
  ring

theorem surjective_profileHeight {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    {δ : Real} (hδ : 0 < δ) (htail : ∀ t, δ ≤ |t| → ρ t = |t|) :
    Surjective (profileHeight ρ) := by
  intro y
  let l := -δ - |y| - 1
  let u := max δ y
  have hl : profileHeight ρ l ≤ y := by
    rw [profileHeight_of_le hδ htail (by dsimp [l]; linarith [abs_nonneg y])]
    dsimp [l]
    nlinarith [sq_nonneg (δ + |y|), abs_nonneg y, neg_abs_le y]
  have hu : y ≤ profileHeight ρ u := by
    rw [profileHeight_of_ge hδ htail (le_max_left _ _)]
    exact le_max_right _ _
  exact intermediate_value_univ l u (contDiff_profileHeight hρ).continuous ⟨hl, hu⟩

def profileHeightDiffeomorph {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (hlower : ∀ s, |s| ≤ ρ s)
    (hderiv : ∀ s, |deriv ρ s| ≤ 1) {δ : Real} (hδ : 0 < δ)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|) : Real ≃ₘ[Real] Real := by
  let D := Plane.fiberDiffeomorph
    ((contDiff_profileHeight hρ).comp
      (contDiff_snd : ContDiff Real ∞ (Prod.snd : Real × Real → Real)))
    (fun _ s => deriv_profileHeight_pos hρ hlower hderiv s)
    (fun _ => surjective_profileHeight hρ hδ htail)
  exact {
    toFun := profileHeight ρ
    invFun := fun y => (D.symm (0, y)).2
    left_inv := fun x => congrArg Prod.snd (D.symm_apply_apply (0, x))
    right_inv := fun y => congrArg Prod.snd (D.apply_symm_apply (0, y))
    contMDiff_toFun := (contDiff_profileHeight hρ).contMDiff
    contMDiff_invFun := (D.symm.contDiff.snd.comp
      (f := fun y : Real => (0, y)) (contDiff_const.prodMk contDiff_id)).contMDiff }

@[simp] theorem profileHeightDiffeomorph_apply {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (hlower : ∀ s, |s| ≤ ρ s)
    (hderiv : ∀ s, |deriv ρ s| ≤ 1) {δ : Real} (hδ : 0 < δ)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|) (s : Real) :
    profileHeightDiffeomorph hρ hlower hderiv hδ htail s = profileHeight ρ s := rfl

theorem exists_smooth_profile {δ : Real} (hδ : 0 < δ) :
    ∃ (ρ : Real → Real) (H : Real ≃ₘ[Real] Real),
      ContDiff Real ∞ ρ ∧ LipschitzWith 1 ρ ∧
      (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) ∧
      (∀ s, |deriv ρ s| ≤ 1) ∧
      (∀ s, δ ≤ |s| → ρ s = |s|) ∧
      (∀ s, H s = profileHeight ρ s) ∧ StrictMono H ∧
      (∀ s, 0 < deriv H s) ∧
      (∀ s, s ≤ -δ → H s = -s^2) ∧
      (∀ s, δ ≤ s → H s = s) := by
  obtain ⟨ρ, hρ, _, hLip, htail, hbound, hderiv⟩ :=
    Plane.exists_smooth_absolute_rounding hδ
  let H := profileHeightDiffeomorph hρ (fun s => (hbound s).1) hderiv hδ htail
  exact ⟨ρ, H, hρ, hLip, hbound, hderiv, htail, fun _ => rfl,
    strictMono_profileHeight hρ (fun s => (hbound s).1) hderiv,
    deriv_profileHeight_pos hρ (fun s => (hbound s).1) hderiv,
    fun _ hs => profileHeight_of_le hδ htail hs,
    fun _ hs => profileHeight_of_ge hδ htail hs⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing
