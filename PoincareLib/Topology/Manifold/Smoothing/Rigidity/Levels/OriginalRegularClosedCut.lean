import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Levels.OriginalCutCapDensity
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonWallComplementBall

/-!
# The actual physical cut is regular closed in the original ambient space

Outside the compact strip use the original domain's interior density.
Inside it use both entire cap disks and the exact cut overlap formula.
This proves no cut halfspace chart or ball conclusion. See039, section4.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

/-- The closure of the complete original cut interior is exactly
the literal physical cut, including all old boundary and cap rims.
No Euclidean interior of the graph model is used. See039. -/
theorem OriginalDiskProduct.closure_interior_cut (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    closure (interior P.cutCarrier) = P.cutCarrier := by
  obtain ⟨hK, hint, _, hoverlap, _, _⟩ := P.cut_geometry hR hopen
  have hC : IsClosed P.closedStrip :=
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
  apply Subset.antisymm
  · exact closure_minimal interior_subset hK.isClosed
  · intro x hx
    by_cases hxC : x ∈ P.closedStrip
    · exact P.endDisks_subset_closure_interior_cut hR hopen (hoverlap.subset ⟨hxC, hx⟩)
    · have hxR : x ∈ R := hx.1
      have hxcl : x ∈ closure (interior R) := he.closure_interior.symm.subset hxR
      have hset : P.closedStripᶜ ∩ interior R = interior P.cutCarrier := by
        rw [hint]
        ext y
        exact and_comm
      rw [← hset]
      exact hC.isOpen_compl.inter_closure ⟨hxC, hxcl⟩

end PoincareMT.M76
