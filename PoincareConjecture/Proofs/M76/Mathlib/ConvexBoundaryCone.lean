import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryRadial
import PoincareConjecture.Proofs.M76.Mathlib.ConicalStar










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} {s : Set E}



theorem linearIndependent_faces_of_space_subset_frontier
    (hcv : Convex ℝ s) (hzero : (0 : E) ∈ interior s) (hK : K.space ⊆ frontier s) :
    ∀ r ∈ K.faces, LinearIndependent ℝ ((↑) : r → E) := by
  intro r hr
  exact (K.indep hr).linearIndependent_of_hull_subset_frontier hcv hzero
    ((K.convexHull_subset_space hr).trans hK)




theorem coneAtZero_space_of_frontier [DecidableEq E]
    (hlin : ∀ r ∈ K.faces, LinearIndependent ℝ ((↑) : r → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (hs : IsCompact s) (hcv : Convex ℝ s) (hzero : (0 : E) ∈ interior s)
    (hspace : K.space = frontier s) : (K.coneAtZero hlin hinj).space = s := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := mem_space_iff.mp hx
    apply convexHull_min (t := s) ?_ hcv hxr
    intro y hy
    by_cases hy0 : y = 0
    · exact hy0.symm ▸ interior_subset hzero
    have hy' : y ∈ r.erase 0 := Finset.mem_erase.mpr ⟨hy0, hy⟩
    have hrK : r.erase 0 ∈ K.faces := hr.2.resolve_left fun he => by simp [he] at hy'
    exact hs.isClosed.frontier_subset
      (hspace ▸ K.subset_space hrK hy')
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact vertices_subset_space (zero_mem_coneAtZero_vertices hlin hinj)
    obtain ⟨y, hy, a, ha, hxy⟩ := hs.exists_frontier_pos_smul hcv hzero hx hx0
    obtain ⟨r, hr, hyr⟩ := mem_space_iff.mp (hspace.symm ▸ hy)
    apply convexHull_subset_space (insert_zero_mem_coneAtZero_faces hlin hinj hr)
    rw [Finset.coe_insert, hxy]
    exact smul_mem_convexHull_insert_zero hyr ⟨ha.1.le, ha.2⟩

end Geometry.SimplicialComplex
