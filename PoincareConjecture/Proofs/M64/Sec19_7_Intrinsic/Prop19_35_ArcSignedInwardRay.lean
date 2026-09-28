import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcInwardRaySign

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_arc_signed_inward_ray_transverse_pos
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {A B p sigma : ℝ}
    (hinj : InjOn gamma (Icc A B)) (hp : p ∈ Ioo A B)
    (hregular : ∀ t ∈ Ioo A B, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : gamma p ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc A B ∪ K) (hfV : frontier V = frontier U)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      gamma p + r • (sigma • quarterTurn (deriv gamma p)) ∈ U)
    {w : AnnulusCoordinates} (hw : inner ℝ (sigma • quarterTurn (deriv gamma p)) w ≠ 0)
    (hwray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • w ∈ closure U) :
    0 < inner ℝ (sigma • quarterTurn (deriv gamma p)) w := by
  rcases hsigma with rfl | rfl
  · simp only [one_smul] at hray hw ⊢
    exact m64Intrinsic_arc_inward_ray_transverse_pos hg hinj hp hregular hK hpK
      hU hV hdisj hfU hfV hray hw hwray
  · let eta : ℝ → AnnulusCoordinates := fun t => gamma (A + B - t)
    have heta : ContDiff ℝ ∞ eta := hg.comp (contDiff_const.sub contDiff_id)
    have hinj' : InjOn eta (Icc A B) := by
      intro s hs t ht heq
      have he := hinj ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
      linarith
    have hpoint : eta (A + B - p) = gamma p := by simp [eta]
    have hderiv : deriv eta (A + B - p) = -deriv gamma p := by
      simp only [eta, deriv_comp_const_sub, sub_sub_cancel]
    have himage : eta '' Icc A B = gamma '' Icc A B := by
      change (gamma ∘ fun t => A + B - t) '' Icc A B = _
      rw [image_comp, image_const_sub_Icc]
      congr 2 <;> ring
    have hregular' (t : ℝ) (ht : t ∈ Ioo A B) : deriv eta t ≠ 0 := by
      simp only [eta, deriv_comp_const_sub]
      exact neg_ne_zero.mpr (hregular _ ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hfront : frontier U = eta '' Icc A B ∪ K := by rw [himage]; exact hfU
    have hray' : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        eta (A + B - p) + r • quarterTurn (deriv eta (A + B - p)) ∈ U := by
      simpa only [hpoint, hderiv, map_neg, neg_one_smul] using hray
    have hw' : inner ℝ (quarterTurn (deriv eta (A + B - p))) w ≠ 0 := by
      simpa only [hderiv, map_neg, neg_one_smul] using hw
    have h := m64Intrinsic_arc_inward_ray_transverse_pos heta hinj'
      (show A + B - p ∈ Ioo A B from ⟨by linarith [hp.2], by linarith [hp.1]⟩)
      hregular' hK (by simpa only [hpoint] using hpK) hU hV hdisj hfront hfV hray' hw'
      (by simpa only [hpoint] using hwray)
    simpa only [hderiv, map_neg, neg_one_smul] using h

end PoincareConjecture
