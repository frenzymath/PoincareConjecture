import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.NormalFaceStar
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.TwoRayProjection

/-!
# Carriers of two-point and empty actual normal links

An actual two-vertex discrete face link projects to precisely the
two-ray star, while an empty link projects to the center. These
are the low-dimensional normal stars used by Cairns 1940,
Section 11, p. 807. See M76 derivation 39.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq E]

/-- A face with exactly two singleton link faces projects to the
entire two-ray star, with its actual projected endpoints.
See Cairns pp. 800, 807 and M76 derivation 39. -/
theorem affine_image_closedFaceStar_twoPoint (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (f : E →ᵃ[ℝ] F)
    (hf : ∀ x ∈ s, f x = 0) {u v : E}
    (hlink : (K.faceLink s).faces = {({u} : Finset E), {v}}) :
    f '' (K.closedFaceStar s).space = twoRayStar (f u) (f v) := by
  rw [K.affine_image_closedFaceStar hs f hf, hlink]
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
    rcases ht with rfl | rfl | rfl
    · have hy0 : y = 0 := by simpa only [Finset.coe_empty, image_empty,
        insert_empty_eq, convexHull_singleton, mem_singleton_iff] using hyt
      subst y
      exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (by
        simpa only [Finset.coe_singleton, image_singleton, convexHull_pair] using hyt)
    · exact Or.inr (by
        simpa only [Finset.coe_singleton, image_singleton, convexHull_pair] using hyt)
  · rintro (hy | hy)
    · refine mem_iUnion₂.mpr ⟨{u}, Or.inr (Or.inl rfl), ?_⟩
      simpa only [Finset.coe_singleton, image_singleton, convexHull_pair] using hy
    · refine mem_iUnion₂.mpr ⟨{v}, Or.inr (Or.inr rfl), ?_⟩
      simpa only [Finset.coe_singleton, image_singleton, convexHull_pair] using hy

/-- An empty actual face link projects to a singleton center.
The source central face is still nonempty.
See Cairns pp. 800, 807 and M76 derivation 39. -/
theorem affine_image_closedFaceStar_emptyLink (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (f : E →ᵃ[ℝ] F)
    (hf : ∀ x ∈ s, f x = 0) (hlink : (K.faceLink s).faces = ∅) :
    f '' (K.closedFaceStar s).space = {0} := by
  rw [K.affine_image_closedFaceStar hs f hf, hlink]
  simp only [insert_empty_eq, mem_singleton_iff, iUnion_iUnion_eq_left,
    Finset.coe_empty, image_empty, convexHull_singleton]

end Geometry.SimplicialComplex
