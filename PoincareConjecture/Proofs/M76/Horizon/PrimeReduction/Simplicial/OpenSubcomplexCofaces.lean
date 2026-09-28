import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIntrinsicDensity










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem coface_mem_of_subcomplex_mem_nhds
    (L D : SimplicialComplex ℝ E) (hDL : D.faces ⊆ L.faces)
    {r : Finset E} (hr : r ∈ L.faces) (x : L.space)
    (hx : (x : E) ∈ intrinsicInterior ℝ (convexHull ℝ (r : Set E)))
    (hnear : (Subtype.val ⁻¹' D.space : Set L.space) ∈ 𝓝 x)
    {t : Finset E} (ht : t ∈ L.faces) (hrt : r ⊆ t) : t ∈ D.faces := by
  obtain ⟨N, hND, hN, hxN⟩ := mem_nhds_iff.mp hnear
  obtain ⟨U, hU, hUN⟩ := isOpen_induced_iff.mp hN
  have hxU : (x : E) ∈ U := (Set.ext_iff.mp hUN x).mpr hxN
  have hxt : (x : E) ∈ convexHull ℝ (t : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr hrt) (intrinsicInterior_subset hx)
  obtain ⟨y, hyt, hyU⟩ :=
    (convex_convexHull ℝ (t : Set E)).intrinsicInterior_inter_open_nonempty hU ⟨x, hxt, hxU⟩
  have hyL : y ∈ L.space := L.convexHull_subset_space ht (intrinsicInterior_subset hyt)
  have hyD : y ∈ D.space := hND ((Set.ext_iff.mp hUN ⟨y, hyL⟩).mp hyU)
  obtain ⟨u, hu, hyu⟩ := mem_space_iff.mp hyD
  exact D.down_closed hu (L.subset_of_mem_intrinsicInterior_face ht (hDL hu) hyt hyu)
    ((L.nonempty_of_mem_faces hr).mono hrt)

end Geometry.SimplicialComplex
