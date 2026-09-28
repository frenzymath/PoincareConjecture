import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.TangentCone.Prod

set_option autoImplicit false

open Set
open scoped ContDiff Topology Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_zero_slice_of_contDiffOn
    {J : Set ℝ} {U : Set E} {f : ℝ × E → F}
    (hJ : UniqueDiffOn ℝ J) (hzero : (0 : ℝ) ∈ J) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) {x : E} (hx : x ∈ U) (r : ℕ) :
    iteratedFDeriv ℝ r (fun y => f (0, y)) x =
      (iteratedFDerivWithin ℝ r f (J ×ˢ U) (0, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  have hpre : L ⁻¹' (J ×ˢ U) = U := by
    ext y
    simp only [mem_preimage, mem_prod, L, ContinuousLinearMap.inr_apply, hzero, true_and]
  have hpre_unique : UniqueDiffOn ℝ (L ⁻¹' (J ×ˢ U)) := hpre.symm ▸ hU.uniqueDiffOn
  have hcomp := L.iteratedFDerivWithin_comp_right hf (hJ.prod hU.uniqueDiffOn)
    hpre_unique ⟨hzero, hx⟩ (i := r) (by exact_mod_cast le_top (a := (r : ℕ∞)))
  rw [hpre, iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) r hU hx] at hcomp
  exact hcomp

theorem iteratedFDeriv_time_slice_of_contDiffOn
    {J : Set ℝ} {U : Set E} {f : ℝ × E → F}
    (hJ : UniqueDiffOn ℝ J) {u : ℝ} (hu : u ∈ J) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) {x : E} (hx : x ∈ U) (r : ℕ) :
    iteratedFDeriv ℝ r (fun y => f (u, y)) x =
      (iteratedFDerivWithin ℝ r f (J ×ˢ U) (u, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  let K : Set ℝ := (fun t => t - u) '' J
  have hK : UniqueDiffOn ℝ K := hJ.image
    (fun t _ => ((hasFDerivAt_id t).sub_const u).hasFDerivWithinAt)
    (fun _ _ => Function.surjective_id.denseRange)
  have hzero : (0 : ℝ) ∈ K := ⟨u, hu, sub_self u⟩
  have hmap : MapsTo (fun p : ℝ × E => (u, 0) + p) (K ×ˢ U) (J ×ˢ U) := by
    rintro p ⟨⟨t, ht, htp⟩, hp⟩
    refine ⟨?_, ?_⟩
    · change u + p.1 ∈ J
      rw [← htp]
      simpa only [add_sub_cancel] using ht
    · simpa only [Prod.snd_add, zero_add] using hp
  have hshift : (u, (0 : E)) +ᵥ (K ×ˢ U) = J ×ˢ U := by
    change (fun p : ℝ × E => (u, 0) + p) '' (K ×ˢ U) = J ×ˢ U
    apply Subset.antisymm (image_subset_iff.mpr hmap)
    intro p hp
    refine ⟨(p.1 - u, p.2), ⟨⟨p.1, hp.1, rfl⟩, hp.2⟩, ?_⟩
    ext <;> simp [add_sub_cancel]
  have hs := hf.comp (contDiff_const.add contDiff_id).contDiffOn hmap
  have hslice := iteratedFDeriv_zero_slice_of_contDiffOn hK hzero hU hs hx r
  dsimp only [Function.comp_def, id_eq] at hslice
  rw [iteratedFDerivWithin_comp_add_left, hshift] at hslice
  simpa only [Function.comp_def, Prod.mk_add_mk, add_zero, zero_add] using hslice

theorem continuousOn_spatial_jet_of_contDiffOn
    {J : Set ℝ} {U : Set E} {f : ℝ × E → F}
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (r : ℕ) :
    ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ r (fun y => f (p.1, y)) p.2)
      (J ×ˢ U) := by
  have hc := hf.continuousOn_iteratedFDerivWithin
    (show (r : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top (a := (r : ℕ∞)))
    (hJ.prod hU.uniqueDiffOn)
  have hlinear := (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := F) (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ E)).continuous
  apply (hlinear.comp_continuousOn hc).congr
  intro p hp
  exact iteratedFDeriv_time_slice_of_contDiffOn hJ hp.1 hU hf hp.2 r

theorem norm_spatial_jet_sub_le_spacetime_jet_sub
    {J K : Set ℝ} {U : Set E} {f g : ℝ × E → F}
    (hJ : UniqueDiffOn ℝ J) (hK : UniqueDiffOn ℝ K)
    (hzeroJ : (0 : ℝ) ∈ J) (hzeroK : (0 : ℝ) ∈ K) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hg : ContDiffOn ℝ ∞ g (K ×ˢ U))
    {x : E} (hx : x ∈ U) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun y => f (0, y)) x -
        iteratedFDeriv ℝ r (fun y => g (0, y)) x‖ ≤
      ‖iteratedFDerivWithin ℝ r f (J ×ˢ U) (0, x) -
        iteratedFDerivWithin ℝ r g (K ×ˢ U) (0, x)‖ := by
  rw [iteratedFDeriv_zero_slice_of_contDiffOn hJ hzeroJ hU hf hx,
    iteratedFDeriv_zero_slice_of_contDiffOn hK hzeroK hU hg hx]
  let L := ContinuousLinearMap.inr ℝ ℝ E
  let B := iteratedFDerivWithin ℝ r f (J ×ˢ U) (0, x) -
    iteratedFDerivWithin ℝ r g (K ×ˢ U) (0, x)
  change ‖B.compContinuousLinearMap (fun _ => L)‖ ≤ ‖B‖
  exact (B.norm_compContinuousLinearMap_le (fun _ => L)).trans
    ((mul_le_mul_of_nonneg_left (Finset.prod_le_one
      (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ ℝ E))
      (norm_nonneg B)).trans_eq (mul_one _))
