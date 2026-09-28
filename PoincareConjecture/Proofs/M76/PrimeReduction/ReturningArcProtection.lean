import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set Geometry Metric

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_subcomplex_of_mem_intrinsicInterior_iff
    {K A : SimplicialComplex ℝ E} (hAK : A ≤ K)
    {s : Finset E} (hs : s ∈ K.faces) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    x ∈ A.space ↔ s ∈ A.faces := by
  constructor
  · intro hxA
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxA
    exact A.down_closed ht
      (K.subset_of_mem_intrinsicInterior_face hs (hAK ht) hx hxt)
      (K.nonempty_of_mem_faces hs)
  · exact fun hsA => convexHull_subset_space hsA (intrinsicInterior_subset hx)

theorem exists_protected_face_bigon_neighborhood
    {K A : SimplicialComplex ℝ E} (hK : K.faces.Finite) (hAK : A ≤ K)
    {s e : Finset E} (hs : s ∈ K.faces) (he : e ∈ K.faces)
    (hsc : s.card = 3) (hec : e.card = 2)
    {p u : E}
    (hps : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hue : u ∈ intrinsicInterior ℝ (convexHull ℝ (e : Set E)))
    (hpA : p ∉ A.space) (huA : u ∉ A.space)
    {D : Set E} (hD : IsCompact D)
    (hDs : D ⊆ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∪
      intrinsicInterior ℝ (convexHull ℝ (e : Set E))) :
    ∃ U : Set E, IsOpen U ∧ D ⊆ U ∧ Disjoint U A.space ∧
      (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ e →
        Disjoint U (convexHull ℝ (t : Set E))) ∧
      ∃ δ : ℝ, 0 < δ ∧ cthickening δ D ⊆ U := by
  classical
  have hsA : s ∉ A.faces := fun h => hpA
    ((mem_subcomplex_of_mem_intrinsicInterior_iff hAK hs hps).mpr h)
  have heA : e ∉ A.faces := fun h => huA
    ((mem_subcomplex_of_mem_intrinsicInterior_iff hAK he hue).mpr h)
  let B : Set (Finset E) := {t ∈ K.faces | t.card ≤ 2 ∧ t ≠ e}
  let Z : Set E := A.space ∪ ⋃ t ∈ B, convexHull ℝ (t : Set E)
  have hB : B.Finite := hK.subset (fun _ ht => ht.1)
  have hZ : IsClosed Z :=
    (A.isCompact_space_of_finite (hK.subset hAK)).isClosed.union
      (hB.isClosed_biUnion fun t _ => (t.finite_toSet.isCompact_convexHull ℝ).isClosed)
  have hDZ : Disjoint D Z := by
    apply Set.disjoint_left.mpr
    intro x hx hxZ
    rcases hxZ with hxA | hxedges
    · rcases hDs hx with hxs | hxe
      · exact hsA ((mem_subcomplex_of_mem_intrinsicInterior_iff hAK hs hxs).mp hxA)
      · exact heA ((mem_subcomplex_of_mem_intrinsicInterior_iff hAK he hxe).mp hxA)
    · obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxedges
      rcases hDs hx with hxs | hxe
      · have hcard := Finset.card_le_card
          (K.subset_of_mem_intrinsicInterior_face hs ht.1 hxs hxt)
        have htcard := ht.2.1
        omega
      · have het := K.subset_of_mem_intrinsicInterior_face he ht.1 hxe hxt
        have htcard := ht.2.1
        exact ht.2.2 (Finset.eq_of_subset_of_card_le het (by omega)).symm
  have hDU : D ⊆ Zᶜ := Set.disjoint_left.mp hDZ
  obtain ⟨δ, hδ, hthick⟩ := hD.exists_cthickening_subset_open hZ.isOpen_compl hDU
  refine ⟨Zᶜ, hZ.isOpen_compl, hDU, ?_, ?_, δ, hδ, hthick⟩
  · exact Set.disjoint_left.mpr fun _ hx hxA => hx (Or.inl hxA)
  · intro t ht htc hte
    exact Set.disjoint_left.mpr fun _ hx hxt =>
      hx (Or.inr (mem_iUnion₂.mpr ⟨t, ⟨ht, htc, hte⟩, hxt⟩))

end Geometry.SimplicialComplex
