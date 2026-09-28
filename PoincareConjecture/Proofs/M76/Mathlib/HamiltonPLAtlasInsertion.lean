import PoincareConjecture.Proofs.M76.Mathlib.HamiltonCompactOverlap
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLChartRestriction

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_compact_core_chart_insertion
    (c : ι → OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (c i).symm.trans (c j) ∈ piecewiseAffineGroupoid E)
    {A B N : Set M} (hA : IsCompact A) (hB : IsCompact B) (hN : IsOpen N)
    (hAU : A ⊆ ⋃ i, (c i).source) (hBV : B ⊆ d.source) (hAB : A ∩ B ⊆ N)
    (hstraight : ∀ i, (c i).symm.trans (d.restr N) ∈ piecewiseAffineGroupoid E) :
    ∃ (U V : Set M) (C : Option ι → OpenPartialHomeomorph M E),
      IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧
      U ⊆ ⋃ i, (c i).source ∧ V ⊆ d.source ∧ U ∩ V ⊆ N ∧
      C none = d.restr V ∧ (∀ i, C (some i) = (c i).restr U) ∧
      (∀ i j, (C i).symm.trans (C j) ∈ piecewiseAffineGroupoid E) ∧
      (⋃ i, (C i).source) = U ∪ V := by
  obtain ⟨U, V, hU, hV, hAC, hBC, hUc, hVd, hUV⟩ :=
    hA.exists_open_shrinkings_inter_subset hB (isOpen_iUnion fun i => (c i).open_source)
      d.open_source hN hAU hBV hAB
  let C : Option ι → OpenPartialHomeomorph M E := fun i =>
    i.elim (d.restr V) (fun j => (c j).restr U)
  have hforward (i : ι) :
      ((c i).restr U).symm.trans (d.restr V) ∈ piecewiseAffineGroupoid E :=
    (c i).restricted_transition_mem_of_overlap d hN hUV (hstraight i)
  refine ⟨U, V, C, hU, hV, hAC, hBC, hUc, hVd, hUV, rfl, fun _ => rfl, ?_, ?_⟩
  · intro i j
    cases i with
    | none =>
      cases j with
      | none => exact (d.restr V).self_transition_mem_piecewiseAffineGroupoid
      | some j =>
        have hj := (piecewiseAffineGroupoid E).symm (hforward j)
        change (d.restr V).symm.trans ((c j).restr U) ∈ piecewiseAffineGroupoid E
        simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm] using hj
    | some i =>
      cases j with
      | none => exact hforward i
      | some j =>
        exact (c i).restricted_transition_mem_piecewiseAffineGroupoid
          (c j) (hcompat i j) U U
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      cases i with
      | none =>
        exact Or.inr (interior_subset hi.2)
      | some i =>
        exact Or.inl (interior_subset hi.2)
    · intro hx
      rcases hx with hxU | hxV
      · obtain ⟨i, hi⟩ := mem_iUnion.mp (hUc hxU)
        refine mem_iUnion.mpr ⟨some i, ?_⟩
        change x ∈ ((c i).restr U).source
        rw [OpenPartialHomeomorph.restr_source' _ _ hU]
        exact ⟨hi, hxU⟩
      · refine mem_iUnion.mpr ⟨none, ?_⟩
        change x ∈ (d.restr V).source
        rw [OpenPartialHomeomorph.restr_source' _ _ hV]
        exact ⟨hVd hxV, hxV⟩

end OpenPartialHomeomorph
