import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralUnions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FinitePiecewiseAffine
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!

# Exact finite images of possibly singular PL maps

Caratheodory reduces arbitrary finite vertex hulls to finitely
many independent simplex hulls. Their exact finite union gives
a triangulation of every finite PL image, retaining original
face containment and dimension bounds even for collapsed or
overlapping images. See Hudson 1969, pp. 12--19, Hatcher's
3-manifold notes, Theorem 3.1, pp. 45--46 and M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A finite union of hulls of arbitrary finite vertex sets
has an exact finite triangulation, subordinate to the original
hulls. The vertex sets may be dependent or empty.
See Hudson pp. 12--19 and M76 derivation 270. -/
theorem exists_finite_triangulation_iUnion_finiteHull
    {ι : Type*} [Finite ι] (T : ι → Finset F) :
    ∃ J : SimplicialComplex ℝ F, J.faces.Finite ∧
      J.space = ⋃ i, convexHull ℝ (T i : Set F) ∧
      ∀ s ∈ J.faces, ∃ i, convexHull ℝ (s : Set F) ⊆ convexHull ℝ (T i : Set F) := by
  classical
  let B : ι → Set (Finset F) := fun i =>
    {t | t ⊆ T i ∧ AffineIndependent ℝ ((↑) : t → F)}
  have hB (i : ι) : (B i).Finite := (T i).powerset.finite_toSet.subset
    (fun t ht => Finset.mem_powerset.mpr ht.1)
  let : ∀ i, Finite (B i) := fun i => (hB i).to_subtype
  obtain ⟨J, hJ, hJs, hfaces⟩ := exists_finite_triangulation_iUnion_convexHull
    (fun p : Σ i, B i => p.2.val) (fun p => p.2.property.2)
  refine ⟨J, hJ, hJs.trans ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨p, hxp⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨p.1,
        convexHull_mono (Finset.coe_subset.mpr p.2.property.1) hxp⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      rw [convexHull_eq_union] at hxi
      simp only [mem_iUnion] at hxi
      obtain ⟨t, ht, hind, hxt⟩ := hxi
      exact mem_iUnion.mpr ⟨⟨i, ⟨t, Finset.coe_subset.mp ht, hind⟩⟩, hxt⟩
  · intro s hs
    obtain ⟨p, hsp⟩ := hfaces s hs
    exact ⟨p.1, hsp.trans (convexHull_mono (Finset.coe_subset.mpr p.2.property.1))⟩

/-- The actual image of a finite face-affine map has a finite
triangulation even when faces collapse or overlap. Every
target face lies in the image of an original source face and
has no larger cardinality. See Hatcher Theorem 3.1, pp. 45--46,
Hudson pp. 15--19 and M76 derivation 270. -/
theorem AffineOnFaces.exists_finite_triangulation_image
    {K : SimplicialComplex ℝ E} {f : E → F} (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) :
    ∃ J : SimplicialComplex ℝ F, J.faces.Finite ∧ J.space = f '' K.space ∧
      ∀ t ∈ J.faces, ∃ s ∈ K.faces,
        convexHull ℝ (t : Set F) ⊆ f '' convexHull ℝ (s : Set E) ∧ t.card ≤ s.card := by
  classical
  let : Finite K.faces := hK.to_subtype
  obtain ⟨J, hJ, hJs, hfaces⟩ := exists_finite_triangulation_iUnion_finiteHull
    (fun s : K.faces => s.val.image f)
  have him (s : K.faces) :
      convexHull ℝ (s.val.image f : Set F) = f '' convexHull ℝ (s.val : Set E) := by
    rw [Finset.coe_image]
    exact (hf.image_convexHull s.property).symm
  refine ⟨J, hJ, ?_, ?_⟩
  · rw [hJs]
    ext y
    constructor
    · intro hy
      obtain ⟨s, hys⟩ := mem_iUnion.mp hy
      rw [him s] at hys
      obtain ⟨x, hx, rfl⟩ := hys
      exact mem_image_of_mem f (K.convexHull_subset_space s.property hx)
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      apply mem_iUnion.mpr
      refine ⟨⟨s, hs⟩, ?_⟩
      rw [him]
      exact mem_image_of_mem f hxs
  · intro t ht
    obtain ⟨s, hts⟩ := hfaces t ht
    have hspan : (t : Set F) ⊆ affineSpan ℝ (s.val.image f : Set F) :=
      (subset_convexHull ℝ _).trans (hts.trans (convexHull_subset_affineSpan _))
    have hcard : t.card ≤ s.val.card :=
      ((J.indep ht).card_le_card_of_subset_affineSpan hspan).trans Finset.card_image_le
    exact ⟨s.val, s.property, (him s) ▸ hts, hcard⟩

end Geometry.SimplicialComplex

namespace Geometry

/-- Every finite PL map has an actual finite polyhedral image,
without an injectivity premise. See Hudson pp. 15--19 and
M76 derivation 270. -/
theorem FinitePiecewiseAffineOn.exists_finite_triangulation_image
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {S : Set E} (hf : FinitePiecewiseAffineOn f S) :
    ∃ J : SimplicialComplex ℝ F, J.faces.Finite ∧ J.space = f '' S := by
  obtain ⟨K, hK, rfl, hfK⟩ := hf
  obtain ⟨J, hJ, hJs, _⟩ := hfK.exists_finite_triangulation_image hK
  exact ⟨J, hJ, hJs⟩

end Geometry
