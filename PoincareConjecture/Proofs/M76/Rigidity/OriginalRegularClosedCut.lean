import PoincareConjecture.Proofs.M76.Rigidity.OriginalCutCapDensity
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}




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

end PoincareConjecture.M76
