import PoincareConjecture.Proofs.M76.Mathlib.PolygonBoundedRegions
import PoincareConjecture.Proofs.M76.Mathlib.ComplementaryRegionClosures









set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}




def inside (P : Polygon E n) : Set E :=
  {q | q ∈ (P.boundary ℝ)ᶜ ∧ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q)}



def outside (P : Polygon E n) : Set E :=
  {q | q ∈ (P.boundary ℝ)ᶜ ∧ ¬ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ q)}



theorem compl_boundary_eq_inside_union_outside (P : Polygon E n) :
    (P.boundary ℝ)ᶜ = P.inside ∪ P.outside := by
  classical
  ext q
  simp only [inside, outside, mem_union, mem_ofPred_eq]
  tauto



theorem disjoint_inside_outside (P : Polygon E n) : Disjoint P.inside P.outside :=
  Set.disjoint_left.mpr fun _ hi ho => ho.2 hi.2




theorem exists_inside_outside_components (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      P.inside = connectedComponentIn (P.boundary ℝ)ᶜ a ∧
      P.outside = connectedComponentIn (P.boundary ℝ)ᶜ b ∧
      Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ b) := by
  obtain ⟨a, ha, b, hb, habound, hbunbound, hcover⟩ :=
    P.exists_bounded_unbounded_complement_components hP hinj
  refine ⟨a, ha, b, hb, ?_, ?_, habound, hbunbound⟩
  · apply Subset.antisymm
    · intro q hq
      rcases hcover ▸ hq.1 with hqa | hqb
      · exact hqa
      · exact (hbunbound (by rw [connectedComponentIn_eq hqb]; exact hq.2)).elim
    · intro q hq
      exact ⟨connectedComponentIn_subset _ _ hq, by rwa [← connectedComponentIn_eq hq]⟩
  · apply Subset.antisymm
    · intro q hq
      rcases hcover ▸ hq.1 with hqa | hqb
      · exact (hq.2 (by rwa [← connectedComponentIn_eq hqa])).elim
      · exact hqb
    · intro q hq
      exact ⟨connectedComponentIn_subset _ _ hq, by rwa [← connectedComponentIn_eq hq]⟩

variable (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)

include hP hinj



theorem isOpen_inside : IsOpen P.inside := by
  obtain ⟨a, _, _, _, hI, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hI]
  exact P.isClosed_boundary.isOpen_compl.connectedComponentIn



theorem isOpen_outside : IsOpen P.outside := by
  obtain ⟨_, _, b, _, _, hO, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hO]
  exact P.isClosed_boundary.isOpen_compl.connectedComponentIn



theorem isConnected_inside : IsConnected P.inside := by
  obtain ⟨a, ha, _, _, hI, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hI]
  exact isConnected_connectedComponentIn_iff.mpr ha



theorem isConnected_outside : IsConnected P.outside := by
  obtain ⟨_, _, b, hb, _, hO, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hO]
  exact isConnected_connectedComponentIn_iff.mpr hb



theorem isBounded_inside : Bornology.IsBounded P.inside := by
  obtain ⟨_, _, _, _, hI, _, hbound, _⟩ := P.exists_inside_outside_components hP hinj
  rwa [hI]



theorem not_isBounded_outside : ¬ Bornology.IsBounded P.outside := by
  obtain ⟨_, _, _, _, _, hO, _, hunbound⟩ := P.exists_inside_outside_components hP hinj
  rwa [hO]



theorem frontier_inside : frontier P.inside = P.boundary ℝ := by
  obtain ⟨a, ha, _, _, hI, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hI]
  exact P.frontier_complement_component hP hinj ha



theorem frontier_outside : frontier P.outside = P.boundary ℝ := by
  obtain ⟨_, _, b, hb, _, hO, _⟩ := P.exists_inside_outside_components hP hinj
  rw [hO]
  exact P.frontier_complement_component hP hinj hb



theorem closure_inside : closure P.inside = P.outsideᶜ :=
  closure_eq_compl_of_complementary_regions P.compl_boundary_eq_inside_union_outside
    P.disjoint_inside_outside (P.frontier_inside hP hinj)



theorem interior_closure_inside : interior (closure P.inside) = P.inside :=
  interior_closure_eq_of_complementary_regions P.compl_boundary_eq_inside_union_outside
    P.disjoint_inside_outside (P.frontier_inside hP hinj) (P.frontier_outside hP hinj)



theorem frontier_closure_inside : frontier (closure P.inside) = P.boundary ℝ :=
  frontier_closure_eq_of_complementary_regions P.compl_boundary_eq_inside_union_outside
    P.disjoint_inside_outside (P.frontier_inside hP hinj) (P.frontier_outside hP hinj)



theorem isCompact_closure_inside : IsCompact (closure P.inside) :=
  (P.isBounded_inside hP hinj).isCompact_closure

end Polygon
