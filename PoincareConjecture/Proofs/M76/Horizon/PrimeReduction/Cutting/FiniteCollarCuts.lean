import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CollarCutCarrier

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem finite_collar_cut_geometry
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Finite ι]
    {R : Set X} {U : ι → Set X} (hR : IsCompact R)
    (hU : ∀ i, IsOpen (U i)) (hinside : ∀ i, closure (U i) ⊆ interior R)
    (hdisjoint : Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j)))) :
    IsCompact (R \ ⋃ i, U i) ∧
      interior (R \ ⋃ i, U i) = interior R \ ⋃ i, closure (U i) ∧
      frontier (R \ ⋃ i, U i) = frontier R ∪ ⋃ i, frontier (U i) ∧
      (∀ i, closure (U i) ∩ (R \ ⋃ j, U j) = frontier (U i)) ∧
      (⋃ i, closure (U i)) ∩ (R \ ⋃ i, U i) = ⋃ i, frontier (U i) ∧
      (⋃ i, closure (U i)) ∪ (R \ ⋃ i, U i) = R ∧
      Pairwise (fun i j => Disjoint (frontier (U i)) (frontier (U j))) ∧
      Disjoint (frontier R) (⋃ i, frontier (U i)) ∧
      frontier R ⊆ R \ ⋃ i, U i := by
  have hopen : IsOpen (⋃ i, U i) := isOpen_iUnion hU
  have hclosure : closure (⋃ i, U i) = ⋃ i, closure (U i) :=
    closure_iUnion_of_finite U
  have hclR : closure (⋃ i, U i) ⊆ interior R := by
    rw [hclosure]
    exact iUnion_subset hinside
  have hfront (i : ι) : frontier (U i) = closure (U i) \ U i := by
    rw [frontier, (hU i).interior_eq]
  have hfrontUnion : frontier (⋃ i, U i) = ⋃ i, frontier (U i) := by
    rw [frontier, hopen.interior_eq, hclosure]
    ext x
    constructor
    · rintro ⟨hx, hxU⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      apply mem_iUnion.mpr
      refine ⟨i, (hfront i).symm.subset ⟨hxi, ?_⟩⟩
      exact fun hu => hxU (mem_iUnion.mpr ⟨i, hu⟩)
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      obtain ⟨hxic, hxin⟩ := (hfront i).subset hxi
      refine ⟨mem_iUnion.mpr ⟨i, hxic⟩, ?_⟩
      intro hxU
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxU
      by_cases hij : i = j
      · subst j
        exact hxin hxj
      · exact disjoint_left.mp (hdisjoint hij) hxic (subset_closure hxj)
  obtain ⟨hcompact, hint, hboundary, hoverlap, hcover, holdnew⟩ :=
    compact_collar_cut_geometry hR hopen hclR
  refine ⟨hcompact, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hclosure] using hint
  · simpa only [hfrontUnion] using hboundary
  · intro i
    rw [hfront i]
    ext x
    constructor
    · rintro ⟨hxi, hxR, hxU⟩
      exact ⟨hxi, fun hu => hxU (mem_iUnion.mpr ⟨i, hu⟩)⟩
    · rintro ⟨hxi, hxin⟩
      refine ⟨hxi, interior_subset (hinside i hxi), ?_⟩
      intro hxU
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxU
      by_cases hij : i = j
      · subst j
        exact hxin hxj
      · exact disjoint_left.mp (hdisjoint hij) hxi (subset_closure hxj)
  · simpa only [hclosure, hfrontUnion] using hoverlap
  · simpa only [hclosure] using hcover
  · intro i j hij
    exact (hdisjoint hij).mono frontier_subset_closure frontier_subset_closure
  · simpa only [hfrontUnion] using holdnew
  · intro x hx
    refine ⟨hR.isClosed.frontier_subset hx, ?_⟩
    intro hxU
    exact hx.2 (hclR (subset_closure hxU))

end PoincareConjecture.M76
