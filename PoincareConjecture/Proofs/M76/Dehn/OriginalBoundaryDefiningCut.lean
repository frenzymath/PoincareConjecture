import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedSignedPLChart

set_option autoImplicit false

open Set Geometry
open scoped BigOperators

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M] [T2Space M]
  [LocallyCompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_PL_defining_cut_near_compact_with_signs
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ y : M, ∃ i, y ∈ (e i).source)
    {R A : Set M} (hA : IsCompact A) (hAR : A ⊆ R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (r : M → ℝ) (W : Set M), IsOpen W ∧ A ⊆ W ∧ Continuous r ∧
      (∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target) ∧
      (∀ y ∈ R, 0 ≤ r y) ∧ (∀ y, y ∉ R → r y ≤ 0) ∧
      (∀ y ∈ frontier R, r y = 0) ∧
      ∀ y ∈ W, (y ∈ R ↔ 0 ≤ r y) ∧
        (y ∈ frontier R ↔ r y = 0) ∧ (y ∈ interior R ↔ 0 < r y) := by
  classical
  have hblock (x : A) :
      ∃ (g : M → ℝ) (V : Set M), IsOpen V ∧ (x : M) ∈ V ∧ Continuous g ∧
        (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
        (∀ y ∈ R, 0 ≤ g y) ∧ (∀ y, y ∉ R → g y ≤ 0) ∧
        (∀ y ∈ frontier R, g y = 0) ∧
        (∀ y ∈ V, y ∈ interior R → 0 < g y) ∧
        ∀ y ∈ V, y ∉ R → g y < 0 := by
    by_cases hx : (x : M) ∈ interior R
    · obtain ⟨w, C, V, _, hCR, hV, hxV, hwc, hwu, hwone, hwzero, hwPL⟩ :=
        exists_compactly_supported_PL_core_cutoff e hcompat hcover
          isCompact_singleton isOpen_interior (singleton_subset_iff.mpr hx)
      have hVC : V ⊆ C := by
        intro y hy
        by_contra hyC
        exact one_ne_zero ((hwone hy).symm.trans (hwzero y hyC))
      refine ⟨w, V, hV, hxV (mem_singleton (x : M)), hwc, hwPL,
        fun y _ => (hwu y).1, ?_, ?_, ?_, ?_⟩
      · intro y hyR
        exact (hwzero y (fun hyC => hyR (interior_subset (hCR hyC)))).le
      · intro y hyR
        exact hwzero y (fun hyC =>
          disjoint_left.mp disjoint_interior_frontier (hCR hyC) hyR)
      · intro y hyV _
        rw [hwone hyV]
        norm_num
      · intro y hyV hyR
        exact (hyR (interior_subset (hCR (hVC hyV)))).elim
    · have hxfront : (x : M) ∈ frontier R :=
        (mem_frontier_iff_notMem_interior (hAR x.property)).mpr hx
      obtain ⟨ell, v, B, hnorm, hxB, _, hBPL, hBR⟩ := hboundary x hxfront
      exact exists_supported_signed_PL_boundary_block e hcompat hcover B ell v hnorm
        hBPL hBR hxB
  choose g V hV hxV hgc hgPL hnonneg hnonpos hzero hpos hneg using hblock
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover V hV
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let W : Set M := ⋃ a ∈ s, V a
  let r : M → ℝ := fun y => ∑ a ∈ s, g a y
  have hrnonneg (y : M) (hy : y ∈ R) : 0 ≤ r y :=
    Finset.sum_nonneg (fun a _ => hnonneg a y hy)
  have hrnonpos (y : M) (hy : y ∉ R) : r y ≤ 0 :=
    Finset.sum_nonpos (fun a _ => hnonpos a y hy)
  have hrzero (y : M) (hy : y ∈ frontier R) : r y = 0 :=
    Finset.sum_eq_zero (fun a _ => hzero a y hy)
  have hrpos (y : M) (hyW : y ∈ W) (hyR : y ∈ interior R) : 0 < r y := by
    obtain ⟨a, ha, hyV⟩ := mem_iUnion₂.mp hyW
    have h := Finset.sum_lt_sum (fun b (_ : b ∈ s) => hnonneg b y (interior_subset hyR))
      ⟨a, ha, hpos a y hyV hyR⟩
    simpa only [Finset.sum_const_zero] using h
  have hrneg (y : M) (hyW : y ∈ W) (hyR : y ∉ R) : r y < 0 := by
    obtain ⟨a, ha, hyV⟩ := mem_iUnion₂.mp hyW
    have h := Finset.sum_lt_sum (fun b (_ : b ∈ s) => hnonpos b y hyR)
      ⟨a, ha, hneg a y hyV hyR⟩
    simpa only [Finset.sum_const_zero] using h
  refine ⟨r, W, isOpen_iUnion (fun a => isOpen_iUnion (fun _ => hV a)), hs,
    continuous_finsetSum s (fun a _ => hgc a), ?_, hrnonneg, hrnonpos, hrzero, ?_⟩
  · intro i
    exact locallyPiecewiseAffineOn_finset_sum s (e i).open_target
      (fun a => g a ∘ (e i).symm) (fun a _ => hgPL a i)
  · intro y hyW
    have hcut : y ∈ R ↔ 0 ≤ r y := by
      refine ⟨hrnonneg y, ?_⟩
      intro hy
      by_contra hyR
      exact (not_le_of_gt (hrneg y hyW hyR)) hy
    refine ⟨hcut, ⟨hrzero y, ?_⟩, ⟨hrpos y hyW, ?_⟩⟩
    · intro hyzero
      have hyR := hcut.mpr hyzero.symm.le
      apply (mem_frontier_iff_notMem_interior hyR).mpr
      intro hyint
      exact (ne_of_gt (hrpos y hyW hyint)) hyzero
    · intro hypos
      have hyR := hcut.mpr hypos.le
      apply (mem_interior_iff_notMem_frontier hyR).mpr
      intro hyfront
      exact (ne_of_gt hypos) (hrzero y hyfront)

theorem exists_PL_defining_cut_near_compact
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ y : M, ∃ i, y ∈ (e i).source)
    {R A : Set M} (hA : IsCompact A) (hAR : A ⊆ R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (r : M → ℝ) (W : Set M), IsOpen W ∧ A ⊆ W ∧ Continuous r ∧
      (∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target) ∧
      ∀ y ∈ W, (y ∈ R ↔ 0 ≤ r y) ∧
        (y ∈ frontier R ↔ r y = 0) ∧ (y ∈ interior R ↔ 0 < r y) := by
  obtain ⟨r, W, hW, hAW, hr, hrPL, _, _, _, hsign⟩ :=
    exists_PL_defining_cut_near_compact_with_signs e hcompat hcover hA hAR hboundary
  exact ⟨r, W, hW, hAW, hr, hrPL, hsign⟩

end OpenPartialHomeomorph
