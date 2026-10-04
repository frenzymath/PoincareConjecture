import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexStrictHalfspaceClosure
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHalfspaceSubcomplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralUnions

/-!
# Finite triangulations of strict halfspace closures

Triangulate the closed halfspace intersection and retain the
simplices having a strictly negative point. Their closed union
is exactly the closure of the negative part. See Alexander 1924,
pp. 7--8, Hudson pp. 12--14 and M76 derivation 155.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The closure of the strictly negative part of a finite
polyhedron has a finite triangulation with exactly that carrier.
Zero-only faces are retained precisely when approached by the
negative part. See M76 derivation 155. -/
theorem exists_finite_triangulation_closure_affine_neg (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = closure (K.space ∩ {x | A x < 0}) := by
  classical
  obtain ⟨J, hJ, hJK⟩ := K.exists_finite_triangulation_inter_halfspaces hK {A}
  have hJspace : J.space = K.space ∩ {x | A x ≤ 0} := by simpa using hJK
  let : Fintype J.faces := hJ.fintype
  let I := {s : J.faces // (convexHull ℝ (s.val : Set E) ∩ {x | A x < 0}).Nonempty}
  have hwhole : K.space ∩ {x | A x < 0} =
      ⋃ i : I, convexHull ℝ (i.val.val : Set E) ∩ {x | A x < 0} := by
    ext x
    constructor
    · intro hx
      have hxJ : x ∈ J.space :=
        hJspace.symm ▸ And.intro hx.1 (show A x ≤ 0 from le_of_lt hx.2)
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxJ
      let i : I := ⟨⟨s, hs⟩, x, hxs, hx.2⟩
      exact mem_iUnion.mpr ⟨i, hxs, hx.2⟩
    · intro hx
      obtain ⟨i, hxi, hxA⟩ := mem_iUnion.mp hx
      have hxJ := J.convexHull_subset_space i.val.property hxi
      rw [hJspace] at hxJ
      exact ⟨hxJ.1, hxA⟩
  have hclosure (i : I) :
      closure (convexHull ℝ (i.val.val : Set E) ∩ {x | A x < 0}) =
        convexHull ℝ (i.val.val : Set E) := by
    apply (convex_convexHull ℝ _).closure_inter_affine_neg
      (i.val.val.finite_toSet.isClosed_convexHull ℝ) A ?_ i.property
    intro x hx
    have hxJ := J.convexHull_subset_space i.val.property hx
    rw [hJspace] at hxJ
    exact hxJ.2
  obtain ⟨L, hL, hspace, _⟩ := exists_finite_triangulation_iUnion_convexHull
    (fun i : I => i.val.val) (fun i => J.indep i.val.property)
  refine ⟨L, hL, ?_⟩
  rw [hwhole, closure_iUnion_of_finite]
  simpa only [hclosure] using hspace

end Geometry.SimplicialComplex
