import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.Counts



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem SourceDoubleComponents.boundary_count_zero_iff_disjoint
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
    {S Q : Set E} {R : Set X} (D : SourceDoubleComponents e f S Q R) :
    doubleBoundaryComponentCount f S Q = 0 ↔ Disjoint (doubleLocusOn f S) Q := by
  have : Finite D.Index := D.finite_components
  rw [D.component_counts.1, Set.ncard_eq_zero (Set.toFinite _)]
  constructor
  · intro hzero
    apply Set.disjoint_left.mpr
    intro x hx hQ
    obtain ⟨i, hi⟩ := mem_iUnion.mp (D.literal_cover.symm.subset hx)
    exact Set.notMem_empty i (hzero ▸ (show (D.pieces i ∩ Q).Nonempty from ⟨x, hi, hQ⟩))
  · intro hdis
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro i ⟨x, hix, hxQ⟩
    exact Set.disjoint_left.mp hdis
      (D.literal_cover.subset (mem_iUnion.mpr ⟨i, hix⟩)) hxQ

end PoincareConjecture.M76.Dehn.Annuli
