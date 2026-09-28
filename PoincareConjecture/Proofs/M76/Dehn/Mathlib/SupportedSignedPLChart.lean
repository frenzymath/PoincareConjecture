import PoincareConjecture.Proofs.M76.Dehn.Mathlib.LocalPLScalarArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLCoreCutoffs
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts

set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M] [T2Space M]
  [LocallyCompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_supported_signed_PL_boundary_block
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ y : M, ∃ i, y ∈ (e i).source)
    {R : Set M} (B : OpenPartialHomeomorph M E) (ell : E →ᴬ[ℝ] ℝ)
    (v : E) (hnorm : ell.contLinear v = 1)
    (hBPL : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E)
    (hBR : ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))
    {x : M} (hxB : x ∈ B.source) :
    ∃ (g : M → ℝ) (V : Set M), IsOpen V ∧ x ∈ V ∧ Continuous g ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      (∀ y ∈ R, 0 ≤ g y) ∧ (∀ y, y ∉ R → g y ≤ 0) ∧
      (∀ y ∈ frontier R, g y = 0) ∧
      (∀ y ∈ V, y ∈ interior R → 0 < g y) ∧
      ∀ y ∈ V, y ∉ R → g y < 0 := by
  classical
  obtain ⟨w, C, V, hC, hCB, hV, hxV, hwc, hwu, hwone, hwzero, hwPL⟩ :=
    exists_compactly_supported_PL_core_cutoff e hcompat hcover
      isCompact_singleton B.open_source (singleton_subset_iff.mpr hxB)
  let g : M → ℝ := B.source.indicator
    (fun y => max (-w y) (min (w y) (ell (B y))))
  have hgon (y : M) (hy : y ∈ B.source) :
      g y = max (-w y) (min (w y) (ell (B y))) := indicator_of_mem hy _
  have hgoff (y : M) (hy : y ∉ B.source) : g y = 0 := indicator_of_notMem hy _
  have hgzero (y : M) (hy : y ∉ C) : g y = 0 := by
    by_cases hyB : y ∈ B.source
    · rw [hgon y hyB, hwzero y hy, neg_zero]
      exact max_eq_left (min_le_left _ _)
    · exact hgoff y hyB
  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hyB : y ∈ B.source
    · have hformula : ContinuousAt
          (fun z => max (-w z) (min (w z) (ell (B z)))) y :=
        hwc.continuousAt.neg.max (hwc.continuousAt.min
          (ell.continuous.continuousAt.comp (B.continuousAt hyB)))
      apply ContinuousAt.congr hformula
      filter_upwards [B.open_source.mem_nhds hyB] with z hz
      exact (hgon z hz).symm
    · apply (continuousAt_const : ContinuousAt (fun _ : M => (0 : ℝ)) y).congr_of_eventuallyEq
      filter_upwards [hC.isClosed.isOpen_compl.mem_nhds
        (show y ∉ C from fun hy => hyB (hCB hy))] with z hz
      exact hgzero z hz
  have hgPL (i : ι) : LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target := by
    let T := (e i).symm.trans B
    have hT : LocallyPiecewiseAffineOn (T : E → E) T.source :=
      ((mem_piecewiseAffineGroupoid_iff E T).mp (hBPL i)).1
    have hell : LocallyPiecewiseAffineOn (ell ∘ T) T.source := by
      simpa only [preimage_univ, inter_univ] using
        (locallyPiecewiseAffineOn_affine ell isOpen_univ).comp hT
    have hwT := (hwPL i).mono T.open_source (fun _ hy => hy.1)
    have hlocal : LocallyPiecewiseAffineOn (g ∘ (e i).symm) T.source := by
      apply (hwT.neg.max (hwT.min hell)).congr
      intro y hy
      exact (hgon ((e i).symm y) hy.2).symm
    let W : Set E := (e i).target ∩ (e i).symm ⁻¹' Cᶜ
    have hW : IsOpen W := (e i).symm.continuousOn.isOpen_inter_preimage
      (e i).open_target hC.isClosed.isOpen_compl
    have hWPL : LocallyPiecewiseAffineOn (g ∘ (e i).symm) W := by
      apply (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ E (0 : ℝ)) hW).congr
      intro y hy
      exact (hgzero ((e i).symm y) hy.2).symm
    apply LocallyPiecewiseAffineOn.locality
    intro y hy
    by_cases hyB : (e i).symm y ∈ B.source
    · exact ⟨T.source, ⟨hy, hyB⟩,
        hlocal.mono ((e i).open_target.inter T.open_source) inter_subset_right⟩
    · exact ⟨W, ⟨hy, fun hz => hyB (hCB hz)⟩,
        hWPL.mono ((e i).open_target.inter hW) inter_subset_right⟩
  have hlin : ell.toAffineMap.linear ≠ 0 := by
    intro hzero
    have hv : ell.toAffineMap.linear v = 1 := hnorm
    rw [hzero, LinearMap.zero_apply] at hv
    exact zero_ne_one hv
  have hfront := B.isImage_frontier_of_affine_nonneg ell hlin hBR
  have hVB : V ⊆ B.source := by
    intro y hy
    apply hCB
    by_contra hyC
    exact one_ne_zero ((hwone hy).symm.trans (hwzero y hyC))
  refine ⟨g, V, hV, hxV (mem_singleton x), hgc, hgPL, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hyR
    by_cases hyB : y ∈ B.source
    · rw [hgon y hyB]
      exact (le_min (hwu y).1 ((hBR y hyB).mp hyR)).trans (le_max_right _ _)
    · exact (hgoff y hyB).symm.le
  · intro y hyR
    by_cases hyB : y ∈ B.source
    · rw [hgon y hyB]
      have hellneg : ell (B y) < 0 := lt_of_not_ge (fun h => hyR ((hBR y hyB).mpr h))
      exact max_le (neg_nonpos.mpr (hwu y).1) ((min_le_right _ _).trans hellneg.le)
    · exact (hgoff y hyB).le
  · intro y hyR
    by_cases hyB : y ∈ B.source
    · rw [hgon y hyB, (hfront.apply_mem_iff hyB).mpr hyR,
        min_eq_right (hwu y).1, max_eq_right (neg_nonpos.mpr (hwu y).1)]
    · exact hgoff y hyB
  · intro y hyV hyR
    have hyB := hVB hyV
    have hnonneg := (hBR y hyB).mp (interior_subset hyR)
    have hne : ell (B y) ≠ 0 := by
      intro hzero
      exact disjoint_left.mp disjoint_interior_frontier hyR
        ((hfront.apply_mem_iff hyB).mp hzero)
    rw [hgon y hyB]
    have hwpos : 0 < w y := by rw [hwone hyV]; norm_num
    exact (lt_min hwpos (lt_of_le_of_ne hnonneg hne.symm)).trans_le (le_max_right _ _)
  · intro y hyV hyR
    have hyB := hVB hyV
    have hellneg : ell (B y) < 0 := lt_of_not_ge (fun h => hyR ((hBR y hyB).mpr h))
    rw [hgon y hyB]
    apply max_lt
    · rw [hwone hyV]
      norm_num
    · exact (min_le_right _ _).trans_lt hellneg

end OpenPartialHomeomorph
