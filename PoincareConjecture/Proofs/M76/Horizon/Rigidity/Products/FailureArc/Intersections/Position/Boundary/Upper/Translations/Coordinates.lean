import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Translations.Crossings
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.UpperTranslation
local notation "P2" => (ℝ × ℝ)

theorem exists_affine_crossing_coordinates
    {u v : P2} (h : LinearIndependent ℝ ![u, v]) (p : P2) :
    ∃ F : P2 ≃ᴬ[ℝ] P2, F 0 = p ∧ ∀ z, F z = z.1 • u + z.2 • v + p := by
  let L : P2 →ₗ[ℝ] P2 :=
    (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight v
  have hL (z : P2) : L z = z.1 • u + z.2 • v := rfl
  have hi : Function.Injective L := by
    intro x y hxy
    have hh : (x.1 - y.1) • u + (x.2 - y.2) • v = 0 := by
      calc
        _ = L x - L y := by rw [hL, hL]; module
        _ = 0 := sub_eq_zero.mpr hxy
    have hz := LinearIndependent.pair_iff.mp h _ _ hh
    exact Prod.ext (sub_eq_zero.mp hz.1) (sub_eq_zero.mp hz.2)
  let B := (LinearEquiv.ofBijective L ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  let F := B.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ P2 p)
  have hF (z : P2) : F z = z.1 • u + z.2 • v + p := add_comm _ _
  exact ⟨F, by rw [hF]; simp, hF⟩

theorem exists_affine_open_segment_crossing
    {a b c d p : P2} (h : LinearIndependent ℝ ![b - a, d - c])
    (hp : p ∈ openSegment ℝ a b ∩ openSegment ℝ c d)
    {O : Set P2} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ (F : P2 ≃ᴬ[ℝ] P2) (U : Set P2),
      IsOpen U ∧ p ∈ U ∧ U ⊆ O ∧ F 0 = p ∧
      (∀ z, F z ∈ U → (F z ∈ segment ℝ a b ↔ z.2 = 0)) ∧
      ∀ z, F z ∈ U → (F z ∈ segment ℝ c d ↔ z.1 = 0) := by
  obtain ⟨t, ht, htp⟩ := (openSegment_eq_image_lineMap ℝ a b).subset hp.1
  obtain ⟨s, hs, hsp⟩ := (openSegment_eq_image_lineMap ℝ c d).subset hp.2
  obtain ⟨F, hFzero, hF⟩ := exists_affine_crossing_coordinates h p
  have hfirst (r : ℝ) : F (r - t, 0) = AffineMap.lineMap a b r := by
    rw [hF, ← htp, AffineMap.lineMap_apply, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  have hsecond (r : ℝ) : F (0, r - s) = AffineMap.lineMap c d r := by
    rw [hF, ← hsp, AffineMap.lineMap_apply, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  let U := O ∩ F.symm ⁻¹' (Ioo (-t) (1 - t) ×ˢ Ioo (-s) (1 - s))
  have hU : IsOpen U := hO.inter ((isOpen_Ioo.prod isOpen_Ioo).preimage F.symm.continuous)
  have hpU : p ∈ U := by
    refine ⟨hpO, ?_⟩
    have hFsymm : F.symm p = 0 := by rw [← hFzero, F.symm_apply_apply]
    change F.symm p ∈ Ioo (-t) (1 - t) ×ˢ Ioo (-s) (1 - s)
    rw [hFsymm]
    change (-t < 0 ∧ 0 < 1 - t) ∧ (-s < 0 ∧ 0 < 1 - s)
    exact ⟨⟨by simpa using ht.1, by linarith [ht.2]⟩,
      ⟨by simpa using hs.1, by linarith [hs.2]⟩⟩
  refine ⟨F, U, hU, hpU, inter_subset_left, hFzero, ?_, ?_⟩
  · intro z hz
    constructor
    · intro hseg
      obtain ⟨r, _, hr⟩ := (segment_eq_image_lineMap ℝ a b).subset hseg
      exact congrArg Prod.snd (F.injective ((hfirst r).trans hr)).symm
    · intro hz0
      have hzrange : z ∈ Ioo (-t) (1 - t) ×ˢ Ioo (-s) (1 - s) := by
        simpa only [Set.mem_preimage, F.symm_apply_apply] using hz.2
      have hr : z.1 + t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hzrange.1.1], by linarith [hzrange.1.2]⟩
      have heq : F z = AffineMap.lineMap a b (z.1 + t) := by
        exact (congrArg F (Prod.ext (by simp : z.1 = z.1 + t - t) hz0)).trans
          (hfirst (z.1 + t))
      rw [heq]
      exact lineMap_mem_segment ℝ a b hr
  · intro z hz
    constructor
    · intro hseg
      obtain ⟨r, _, hr⟩ := (segment_eq_image_lineMap ℝ c d).subset hseg
      exact congrArg Prod.fst (F.injective ((hsecond r).trans hr)).symm
    · intro hz0
      have hzrange : z ∈ Ioo (-t) (1 - t) ×ˢ Ioo (-s) (1 - s) := by
        simpa only [Set.mem_preimage, F.symm_apply_apply] using hz.2
      have hr : z.2 + s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hzrange.2.1], by linarith [hzrange.2.2]⟩
      have heq : F z = AffineMap.lineMap c d (z.2 + s) := by
        exact (congrArg F (Prod.ext hz0 (by simp : z.2 = z.2 + s - s))).trans
          (hsecond (z.2 + s))
      rw [heq]
      exact lineMap_mem_segment ℝ c d hr

end PoincareConjecture.M76.UpperTranslation
