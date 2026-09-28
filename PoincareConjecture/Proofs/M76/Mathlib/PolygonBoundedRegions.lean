import PoincareConjecture.Proofs.M76.Mathlib.PolygonJordanSeparation
import PoincareConjecture.Proofs.M76.Mathlib.UnboundedComplementComponent

set_option autoImplicit false

open Set

namespace Polygon

theorem isCompact_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (P : Polygon E n) : IsCompact (P.boundary ℝ) := by
  apply isCompact_iUnion
  intro i
  rw [P.edgeSet_eq_convexHull]
  exact (P.edgeVertices i).finite_toSet.isCompact_convexHull ℝ

variable {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)

include hP hinj

theorem exists_bounded_unbounded_complement_components :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ b) ∧
      (P.boundary ℝ)ᶜ = connectedComponentIn (P.boundary ℝ)ᶜ a ∪
        connectedComponentIn (P.boundary ℝ)ᶜ b := by
  have hdim : 1 < Module.rank ℝ (ℝ × ℝ) := by
    rw [← Module.finrank_eq_rank]
    norm_num [Module.finrank_prod]
  obtain ⟨x, hx, hxunbounded, hother⟩ :=
    P.isCompact_boundary.isBounded.exists_unique_unbounded_complement_component hdim
  obtain ⟨a, ha, b, hb, hne, hcover⟩ := P.exists_distinct_two_complement_components hP hinj
  have hxcover : x ∈ connectedComponentIn (P.boundary ℝ)ᶜ a ∪
      connectedComponentIn (P.boundary ℝ)ᶜ b := hcover ▸ hx
  rcases hxcover with hxa | hxb
  · have heq := connectedComponentIn_eq hxa
    refine ⟨b, hb, a, ha, hother b ?_, ?_, ?_⟩
    · exact fun h => hne (heq.trans h.symm)
    · rwa [heq]
    · rwa [union_comm]
  · have heq := connectedComponentIn_eq hxb
    refine ⟨a, ha, b, hb, hother a ?_, ?_, hcover⟩
    · exact fun h => hne (h.trans heq.symm)
    · rwa [heq]

theorem exists_bounded_complementary_regions :
    ∃ U V : Set (ℝ × ℝ), IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ (P.boundary ℝ)ᶜ = U ∪ V ∧
      frontier U = P.boundary ℝ ∧ frontier V = P.boundary ℝ ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V := by
  obtain ⟨a, ha, b, hb, habounded, hbunbounded, hcover⟩ :=
    P.exists_bounded_unbounded_complement_components hP hinj
  refine ⟨connectedComponentIn (P.boundary ℝ)ᶜ a,
    connectedComponentIn (P.boundary ℝ)ᶜ b,
    P.isClosed_boundary.isOpen_compl.connectedComponentIn,
    P.isClosed_boundary.isOpen_compl.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr ha,
    isConnected_connectedComponentIn_iff.mpr hb, ?_, hcover,
    P.frontier_complement_component hP hinj ha,
    P.frontier_complement_component hP hinj hb, habounded, hbunbounded⟩
  refine Set.disjoint_left.mpr fun _ hqa hqb => hbunbounded ?_
  rwa [← (connectedComponentIn_eq hqa).trans (connectedComponentIn_eq hqb).symm]

end Polygon
