import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalLineModel
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSeparation

set_option autoImplicit false

open Set

namespace Polygon

variable {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)

include hP hinj

theorem isConnected_boundary : IsConnected (P.boundary ℝ) := by
  obtain ⟨e⟩ := P.nonempty_boundary_homeomorph_circle hP hinj
  exact isConnected_iff_connectedSpace.mpr
    (e.connectedSpace_iff.mpr inferInstance)

theorem frontier_complement_component {q : ℝ × ℝ} (hq : q ∈ (P.boundary ℝ)ᶜ) :
    frontier (connectedComponentIn (P.boundary ℝ)ᶜ q) = P.boundary ℝ :=
  (P.hasLocalComplementarySides_boundary hP hinj).frontier_component_eq
    P.isClosed_boundary (P.isConnected_boundary hP hinj) hq

theorem exists_two_complement_components :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      (P.boundary ℝ)ᶜ = connectedComponentIn (P.boundary ℝ)ᶜ a ∪
        connectedComponentIn (P.boundary ℝ)ᶜ b := by
  obtain ⟨a, ha, b, hb, hcomponents⟩ :=
    (P.hasLocalComplementarySides_boundary hP hinj).exists_two_components
      P.isClosed_boundary (P.isConnected_boundary hP hinj)
  refine ⟨a, ha, b, hb, Subset.antisymm ?_ ?_⟩
  · intro q hq
    rcases hcomponents q hq with heq | heq
    · exact Or.inl (heq ▸ mem_connectedComponentIn hq)
    · exact Or.inr (heq ▸ mem_connectedComponentIn hq)
  · exact union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)

theorem exists_distinct_two_complement_components_of_nonvertical
    (hnv : P.HasNonverticalEdges) :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      connectedComponentIn (P.boundary ℝ)ᶜ a ≠ connectedComponentIn (P.boundary ℝ)ᶜ b ∧
      (P.boundary ℝ)ᶜ = connectedComponentIn (P.boundary ℝ)ᶜ a ∪
        connectedComponentIn (P.boundary ℝ)ᶜ b := by
  obtain ⟨a, ha, b, hb, hcover⟩ := P.exists_two_complement_components hP hinj
  refine ⟨a, ha, b, hb, ?_, hcover⟩
  intro heq
  have hsingle : (P.boundary ℝ)ᶜ = connectedComponentIn (P.boundary ℝ)ᶜ b := by
    simpa only [heq, union_self] using hcover
  apply P.not_isPreconnected_compl_of_nonvertical hP hinj hnv
  rw [hsingle]
  exact isPreconnected_connectedComponentIn

end Polygon
