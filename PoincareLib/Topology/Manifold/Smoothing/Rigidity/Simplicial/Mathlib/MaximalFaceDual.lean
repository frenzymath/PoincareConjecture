import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricDualEdgeDisk

/-!
# The whole dual of an actual maximal face

Every vertex of every retained centroid chain is the same original
centroid. This applies in the unrestricted graph ambient space.
See Hudson1969, pp.8--9 and rigidity025, section1.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

/-- Actual maximality makes the entire dual carrier the original
face centroid. No ambient dimension is assumed. See rigidity025. -/
theorem barycentricDualBlock_space_eq_singleton_of_maximal
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s) :
    (K.barycentricDualBlock s).space = {s.centroid ℝ id} := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
    have hverts : (a : Set E) ⊆ {s.centroid ℝ id} := by
      intro y hy
      obtain ⟨t, ht, hst, hty⟩ := ha.2 y hy
      exact hty.symm.trans (congrArg (fun v : Finset E => v.centroid ℝ id)
        (hmax t ht hst))
    simpa only [convexHull_singleton] using convexHull_mono hverts hxa
  · rintro x rfl
    exact (K.barycentricDualBlock s).vertices_subset_space
      (K.faceCentroid_mem_barycentricDualBlock_vertices hs)

end Geometry.SimplicialComplex
