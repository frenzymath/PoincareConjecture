import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexCapFlattening
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexFrontierSubcomplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHalfspaceSubcomplex

/-!
# Automatic PL flattening of polyhedral convex caps

The boundary subcomplex and a single halfspace subdivision
supply the exact triangulation required for cap flattening.
See Hudson 1969, pp. 12--19 and M76 derivation 134.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite triangulation of the whole convex body supplies
a rim-fixing finite PL map of its far boundary to any closed
unit plane section. No cap triangulation is assumed.
See M76 derivation 134. -/
theorem exists_finitePL_polyhedral_cap_flattening (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hs0 : (0 : E) ∈ interior s) (hspace : K.space = s) (L : E →ₗ[ℝ] ℝ) :
    ∃ e : (frontier s ∩ {x | 1 ≤ L x} : Set E) ≃ₜ (s ∩ {x | L x = 1} : Set E),
      e.IsFinitePL ∧
      (∀ x : (frontier s ∩ {x | 1 ≤ L x} : Set E),
        L (x : E) = 1 → (e x : E) = x) ∧
      (∀ x : (frontier s ∩ {x | 1 ≤ L x} : Set E),
        L (x : E) = 1 ↔ (e x : E) ∈ frontier s) := by
  classical
  let A : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E 1 - L.toAffineMap
  obtain ⟨J, hJ, hJs⟩ := (K.frontierSubcomplex s).exists_finite_triangulation_inter_halfspaces
    (K.frontierSubcomplex_finite s hK) {A}
  rw [K.frontierSubcomplex_space hs.isClosed hcv ⟨0, hs0⟩ hspace] at hJs
  have heq : {x | ∀ B ∈ ({A} : Finset (E →ᵃ[ℝ] ℝ)), B x ≤ 0} = {x | 1 ≤ L x} := by
    ext x
    simp only [Finset.mem_singleton, forall_eq, A, AffineMap.coe_sub, Pi.sub_apply,
      AffineMap.const_apply, LinearMap.coe_toAffineMap, sub_nonpos, mem_ofPred_eq]
  rw [heq] at hJs
  exact J.exists_finitePL_frontier_cap_flattening hJ hs hcv hs0 L hJs

end Geometry.SimplicialComplex
