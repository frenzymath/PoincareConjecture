import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Smooth.LastContact

/-!
# Choosing the base orientation at an actual last contact

The sign of the actual nonzero tangent multiplier selects which original
base endpoint precedes the contact. Full and selected images are retained.
Source: MT Claim 19.40; minimal-contact derivation, Section 11.
-/

noncomputable section
set_option autoImplicit false

open Set Function
open scoped Topology ContDiff

namespace PoincareMT

/-- Orient the original base so that its incoming tangent is positively proportional to the
actual outgoing tail tangent. The selected subarc is literally one of the two original
subarcs. Source: MT Claim 19.40, pp. 470-471;
`proof-work/tasks/M64/derivations/2026-09-27-minimal-contact-regularity.md`, Section 11. -/
theorem m64Intrinsic_exists_positive_contact_base_orientation
    {base eta : ℝ → AnnulusCoordinates} (hb : ContDiff ℝ ∞ base)
    {D p u c : ℝ} (hp : p ∈ Ioo 0 D) (hbi : InjOn base (Icc 0 D))
    (hc : c ≠ 0) (hderiv : deriv eta u = c • deriv base p) :
    ∃ reverse : Bool,
      let zeta : ℝ → AnnulusCoordinates := fun t => base (if reverse then D - t else t)
      let q := if reverse then D - p else p
      let k := if reverse then -c else c
      0 < k ∧ q ∈ Ioo 0 D ∧ ContDiff ℝ ∞ zeta ∧ InjOn zeta (Icc 0 D) ∧
      zeta q = base p ∧ deriv eta u = k • deriv zeta q ∧
      zeta '' Icc 0 D = base '' Icc 0 D ∧
      zeta '' Icc 0 q = if reverse then base '' Icc p D else base '' Icc 0 p := by
  by_cases hpos : 0 < c
  · refine ⟨false, ?_⟩
    dsimp only
    exact ⟨hpos, hp, hb, hbi, rfl, hderiv, rfl, rfl⟩
  have hneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hc
  let zeta : ℝ → AnnulusCoordinates := fun t => base (D - t)
  have hz : ContDiff ℝ ∞ zeta := hb.comp (contDiff_const.sub contDiff_id)
  have hzi : InjOn zeta (Icc 0 D) := by
    intro s hs t ht hst
    have hh := hbi
      (show D - s ∈ Icc 0 D from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (show D - t ∈ Icc 0 D from ⟨by linarith [ht.2], by linarith [ht.1]⟩) hst
    linarith
  have hzderiv : deriv zeta (D - p) = -deriv base p := by
    have hd : HasDerivAt base (deriv base p) (D - (D - p)) := by
      simpa only [sub_sub_cancel] using (hb.differentiable (by simp) p).hasDerivAt
    have hh := hd.scomp (D - p) ((hasDerivAt_id (D - p)).const_sub D)
    simpa only [zeta, Function.comp_def, id_eq, neg_one_smul] using hh.deriv
  have himage : zeta '' Icc 0 D = base '' Icc 0 D := by
    change (base ∘ fun t => D - t) '' Icc 0 D = _
    rw [image_comp, image_const_sub_Icc]
    simp only [sub_self, sub_zero]
  have hsubimage : zeta '' Icc 0 (D - p) = base '' Icc p D := by
    change (base ∘ fun t => D - t) '' Icc 0 (D - p) = _
    rw [image_comp, image_const_sub_Icc]
    simp only [sub_sub_cancel, sub_zero]
  refine ⟨true, ?_⟩
  dsimp only
  simp only [↓reduceIte]
  refine ⟨neg_pos.mpr hneg, ⟨by linarith [hp.2], by linarith [hp.1]⟩,
    hz, hzi, by simp only [sub_sub_cancel], ?_, himage, hsubimage⟩
  change deriv eta u = (-c) • deriv zeta (D - p)
  rw [hzderiv, neg_smul_neg]
  exact hderiv

end PoincareMT
