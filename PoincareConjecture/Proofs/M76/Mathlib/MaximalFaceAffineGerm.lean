import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_open_eq_affineSpan_of_maximal_face
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s)
    {p : E} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      K.space ∩ U = (affineSpan ℝ (s : Set E) : Set E) ∩ U := by
  classical
  let T := {t : Finset E | t ∈ K.faces ∧ t ≠ s}
  have hT : T.Finite := hK.subset fun _ ht => ht.1
  let D := ⋃ t ∈ T, convexHull ℝ (t : Set E)
  have hD : IsClosed D :=
    (hT.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hpD : p ∉ D := by
    intro hpD
    obtain ⟨t, ht, hpt⟩ := mem_iUnion₂.mp hpD
    exact ht.2 (hmax t ht.1 (K.subset_of_mem_intrinsicInterior_face hs ht.1 hp hpt))
  obtain ⟨q, hq, hqp⟩ := mem_intrinsicInterior.mp hp
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior
      ((Subtype.val : affineSpan ℝ (convexHull ℝ (s : Set E)) → E) ⁻¹'
        convexHull ℝ (s : Set E))))
  have hpO : p ∈ O := by
    rw [← hqp]
    exact hOeq.symm.subset hq
  have hOhull : O ∩ (affineSpan ℝ (s : Set E) : Set E) ⊆
      convexHull ℝ (s : Set E) := by
    intro x hx
    have hxspan : x ∈ (affineSpan ℝ (convexHull ℝ (s : Set E)) : Set E) := by
      rw [affineSpan_convexHull]
      exact hx.2
    have hxi : (⟨x, hxspan⟩ : affineSpan ℝ (convexHull ℝ (s : Set E))) ∈
        interior ((Subtype.val : affineSpan ℝ (convexHull ℝ (s : Set E)) → E) ⁻¹'
          convexHull ℝ (s : Set E)) := hOeq.subset hx.1
    have hxmem : (⟨x, hxspan⟩ : affineSpan ℝ (convexHull ℝ (s : Set E))) ∈
        (Subtype.val : affineSpan ℝ (convexHull ℝ (s : Set E)) → E) ⁻¹'
          convexHull ℝ (s : Set E) := interior_subset hxi
    exact hxmem
  refine ⟨O ∩ Dᶜ, hO.inter hD.isOpen_compl, ⟨hpO, hpD⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨hxK, hxU⟩
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxK
    have hts : t = s := by
      by_contra hts
      exact hxU.2 (mem_iUnion₂.mpr ⟨t, ⟨ht, hts⟩, hxt⟩)
    subst t
    exact ⟨convexHull_subset_affineSpan _ hxt, hxU⟩
  · rintro ⟨hxspan, hxU⟩
    exact ⟨K.convexHull_subset_space hs (hOhull ⟨hxU.1, hxspan⟩), hxU⟩

theorem exists_open_eq_affineSpan_of_triangle_interior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {p : E} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      K.space ∩ U = (affineSpan ℝ (s : Set E) : Set E) ∩ U := by
  apply K.exists_open_eq_affineSpan_of_maximal_face hK hs ?_ hp
  intro t ht hst
  exact (Finset.eq_of_subset_of_card_le hst (by simpa only [hcard] using hbound t ht)).symm

end Geometry.SimplicialComplex
