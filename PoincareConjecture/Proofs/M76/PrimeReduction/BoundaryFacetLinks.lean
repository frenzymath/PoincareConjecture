import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem faceLink_ncard_eq_one_of_halfspace
    (K : SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (hscard : s.card = Module.finrank ℝ E)
    (ht : t ∈ K.faces) (hst : s ⊆ t)
    (htcard : t.card = Module.finrank ℝ E + 1)
    (ell : E →ᴬ[ℝ] ℝ) (v : E) (hv : ell.contLinear v = 1)
    (hhalf : K.space ⊆ {x | 0 ≤ ell x})
    (hzero : ∀ x ∈ convexHull ℝ (s : Set E), ell x = 0) :
    (K.faceLink s).vertices.ncard = 1 := by
  classical
  obtain ⟨x, hxs⟩ := (intrinsicInterior_nonempty
    (convex_convexHull ℝ (s : Set E))).mpr
      (show (s : Set E).Nonempty from K.nonempty_of_mem_faces hs).convexHull
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    exact zero_ne_one hval
  have hopen : IsOpenMap (ell : E → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
    (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
  have hunique (u : Finset E) (hu : u ∈ K.faces)
      (hucard : u.card = Module.finrank ℝ E + 1) (hsu : s ⊆ u) : u = t := by
    by_contra hut
    have hxint := K.mem_interior_space_of_paired_facet
      hscard ht hu htcard hucard hst hsu (Ne.symm hut) hxs
    have hxhalf : x ∈ interior ((ell : E → ℝ) ⁻¹' Ici 0) :=
      interior_mono hhalf hxint
    have hxpos := hopen.interior_preimage_subset_preimage_interior hxhalf
    have hxzero := hzero x (intrinsicInterior_subset hxs)
    simp only [mem_preimage, interior_Ici, mem_Ioi, hxzero, lt_self_iff_false] at hxpos
  rw [K.ncard_faceLink_vertices_eq_cofaces]
  apply ncard_eq_one.mpr
  refine ⟨t, ?_⟩
  ext u
  constructor
  · rintro ⟨hu, hucard, hsu⟩
    exact mem_singleton_iff.mpr (hunique u hu (by omega) hsu)
  · intro hu
    rcases mem_singleton_iff.mp hu with rfl
    exact ⟨ht, by omega, hst⟩

end Geometry.SimplicialComplex
