import PoincareConjecture.Proofs.M76.Dehn.Mathlib.LocalPLScalarArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLCoreCutoffs











set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace OpenPartialHomeomorph

variable {X E ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]




theorem exists_supported_PL_scalar_extension
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    {A U : Set X} (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    {f : X → ℝ} (hf : ContinuousOn f U)
    (hfPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U))
    {r : ℝ} (hr : 0 < r) (hbound : ∀ x ∈ A, |f x| ≤ r) :
    ∃ (g : X → ℝ) (C : Set X), IsCompact C ∧ C ⊆ U ∧ Continuous g ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      EqOn g f A ∧ (∀ x, |g x| ≤ r) ∧ (∀ x, x ∉ C → g x = 0) := by
  classical
  obtain ⟨w, C, V, hC, hCU, _, hAV, hwc, hwu, hwone, hwzero, hwPL⟩ :=
    exists_compactly_supported_PL_core_cutoff e hcompat hcover hA hU hAU
  let b := fun x => r * w x
  let g := U.indicator (fun x => Max.max (-b x) (Min.min (b x) (f x)))
  have hbc : Continuous b := continuous_const.mul hwc
  have hbnonneg (x : X) : 0 ≤ b x := mul_nonneg hr.le (hwu x).1
  have hbsmall (x : X) : b x ≤ r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hwu x).2 hr.le
  have hgon (x : X) (hx : x ∈ U) :
      g x = Max.max (-b x) (Min.min (b x) (f x)) := indicator_of_mem hx _
  have hgoff (x : X) (hx : x ∉ C) : g x = 0 := by
    by_cases hxU : x ∈ U
    · rw [hgon x hxU]
      have hb : b x = 0 := by simp only [b, hwzero x hx, mul_zero]
      rw [hb, neg_zero]
      exact max_eq_left (min_le_left _ _)
    · exact indicator_of_notMem hxU _
  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hxU : x ∈ U
    · apply ContinuousAt.congr
        (hbc.continuousAt.neg.max (hbc.continuousAt.min (hf.continuousAt (hU.mem_nhds hxU))))
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact (hgon y hy).symm
    · apply (continuousAt_const : ContinuousAt (fun _ : X => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [hC.isClosed.isOpen_compl.mem_nhds
        (show x ∉ C from fun hx => hxU (hCU hx))] with y hy
      exact hgoff y hy
  refine ⟨g, C, hC, hCU, hgc, ?_, ?_, ?_, hgoff⟩
  · intro i
    let T := (e i).target ∩ (e i).symm ⁻¹' U
    have hT : IsOpen T := (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hU
    have hbPL : LocallyPiecewiseAffineOn (b ∘ (e i).symm) (e i).target := by
      let a := (r • ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap
      have h := (locallyPiecewiseAffineOn_affine a isOpen_univ).comp (hwPL i)
      rw [preimage_univ, inter_univ] at h
      exact h.congr (fun _ _ => rfl)
    have hbT := hbPL.mono hT inter_subset_left
    have hgT : LocallyPiecewiseAffineOn (g ∘ (e i).symm) T := by
      apply (hbT.neg.max (hbT.min (hfPL i))).congr
      intro y hy
      exact (hgon ((e i).symm y) hy.2).symm
    let W := (e i).target ∩ (e i).symm ⁻¹' Cᶜ
    have hW : IsOpen W := (e i).symm.continuousOn.isOpen_inter_preimage
      (e i).open_target hC.isClosed.isOpen_compl
    have hgW : LocallyPiecewiseAffineOn (g ∘ (e i).symm) W := by
      apply (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ E (0 : ℝ)) hW).congr
      intro y hy
      exact (hgoff ((e i).symm y) hy.2).symm
    apply LocallyPiecewiseAffineOn.locality
    intro y hy
    by_cases hyU : (e i).symm y ∈ U
    · exact ⟨T, ⟨hy, hyU⟩, hgT.mono ((e i).open_target.inter hT) inter_subset_right⟩
    · exact ⟨W, ⟨hy, fun h => hyU (hCU h)⟩,
        hgW.mono ((e i).open_target.inter hW) inter_subset_right⟩
  · intro x hx
    rw [hgon x (hAU hx)]
    have hb : b x = r := by simp only [b, hwone (hAV hx), mul_one]
    rw [hb, min_eq_right (abs_le.mp (hbound x hx)).2,
      max_eq_right (abs_le.mp (hbound x hx)).1]
  · intro x
    by_cases hxU : x ∈ U
    · rw [hgon x hxU]
      apply abs_le.mpr
      exact ⟨(neg_le_neg (hbsmall x)).trans (le_max_left _ _),
        max_le ((neg_nonpos.mpr (hbnonneg x)).trans hr.le)
          ((min_le_left _ _).trans (hbsmall x))⟩
    · rw [show g x = 0 from indicator_of_notMem hxU _, abs_zero]
      exact hr.le

end OpenPartialHomeomorph
