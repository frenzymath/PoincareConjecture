import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.SimplexExtremeFaces










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsSubdivision.vertices_subset {K L : SimplicialComplex ℝ E}
    (hLK : L.IsSubdivision K) : K.vertices ⊆ L.vertices := by
  classical
  intro p hp
  obtain ⟨s, hs, hps⟩ := mem_space_iff.mp
    (hLK.space_eq.symm.subset (K.vertices_subset_space hp))
  obtain ⟨t, ht, hst⟩ := hLK.face_subset s hs
  have hpt : p ∈ t := (K.vertex_mem_convexHull_iff hp ht).mp (hst hps)
  have hext : IsExtreme ℝ (convexHull ℝ (t : Set E)) ({p} : Set E) := by
    simpa only [Finset.coe_singleton, convexHull_singleton] using
      (K.indep ht).isExtreme_convexHull_finset_subset (Finset.singleton_subset_iff.mpr hpt)
  have hpext : p ∈ (convexHull ℝ (s : Set E)).extremePoints ℝ :=
    (hext.mono hst (singleton_subset_iff.mpr hps)).mem_extremePoints
  have hpsv : p ∈ s := extremePoints_convexHull_subset hpext
  exact L.down_closed hs (Finset.singleton_subset_iff.mpr hpsv)
    (Finset.singleton_nonempty p)

end Geometry.SimplicialComplex
