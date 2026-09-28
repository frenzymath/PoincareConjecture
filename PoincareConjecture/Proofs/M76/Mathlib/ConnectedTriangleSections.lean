import PoincareConjecture.Proofs.M76.Mathlib.FiniteSurfaceSectionMarks
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage
import Mathlib.Topology.Connected.Clopen










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exists_triangle_containing_connected_height_section
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) (c : ℝ) {T : Set E} (hT : IsConnected T)
    (hTS : T ⊆ K.space ∩ {x | A x = c})
    (havoid : Disjoint T (K.oneSkeletonHeightSection A c)) :
    ∃ s ∈ K.faces, s.card = 3 ∧
      T ⊆ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  have htriangle (x : E) (hx : x ∈ T) :=
    K.exists_triangle_intrinsicInterior_of_notMem_oneSkeletonHeightSection hpure A
      (hTS hx) (fun h => disjoint_left.mp havoid hx h)
  obtain ⟨p, hp⟩ := hT.nonempty
  obtain ⟨s, hs, hsc, hps⟩ := htriangle p hp
  have hinside {x : E} (hx : x ∈ T) (hxs : x ∈ convexHull ℝ (s : Set E)) :
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    obtain ⟨u, hu, huc, hxu⟩ := htriangle x hx
    have hus : u ⊆ s := K.subset_of_mem_intrinsicInterior_face hu hs hxu hxs
    have heq : u = s := Finset.eq_of_subset_of_card_le hus (by omega)
    exact heq ▸ hxu
  let F := {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ t ≠ s}
  let D := ⋃ t ∈ F, convexHull ℝ (t : Set E)
  have hF : F.Finite := hK.subset fun _ ht => ht.1
  have hD : IsClosed D :=
    (hF.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hnotD {x : E} (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
      x ∉ D := by
    intro hxD
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxD
    have hst : s ⊆ t := K.subset_of_mem_intrinsicInterior_face hs ht.1 hxs hxt
    exact ht.2.2 (Finset.eq_of_subset_of_card_le hst (by have := ht.2.1; omega)).symm
  have hcover : T ⊆ convexHull ℝ (s : Set E) ∪ D := by
    intro x hx
    obtain ⟨t, ht, htc, hxt⟩ := htriangle x hx
    by_cases hts : t = s
    · exact Or.inl (hts ▸ intrinsicInterior_subset hxt)
    · exact Or.inr (mem_iUnion₂.mpr ⟨t, ⟨ht, htc, hts⟩, intrinsicInterior_subset hxt⟩)
  have hdisj : T ∩ (convexHull ℝ (s : Set E) ∩ D) = ∅ := by
    apply Subset.antisymm ?_ (empty_subset _)
    intro x hx
    exact (hnotD (hinside hx.1 hx.2.1) hx.2.2).elim
  have hsub : T ⊆ convexHull ℝ (s : Set E) :=
    ((isPreconnected_iff_subset_of_disjoint_closed.mp hT.isPreconnected)
      (convexHull ℝ (s : Set E)) D (s.finite_toSet.isClosed_convexHull ℝ)
      hD hcover hdisj).resolve_right (fun h => hnotD hps (h hp))
  exact ⟨s, hs, hsc, fun x hx => hinside hx (hsub hx)⟩

end Geometry.SimplicialComplex
