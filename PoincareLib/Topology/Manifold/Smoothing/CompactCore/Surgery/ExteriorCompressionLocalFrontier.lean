import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Surgery.ProtectedBlockFrontier
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.General.OppositePLDomain
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Regions.Mathlib.ProtectedFrontier

/-! # The literal local frontier for exterior compression -/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exterior_compression_local_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K H L Y F : Set X}
    (hK : PLDomain e K) (hH : PLDomain e H) (hKH : K ⊆ interior H)
    (hL : L = H ∩ (interior K)ᶜ) (hcut : Y ∩ frontier K = F) :
    (interior H ∩ Y) ∩ frontier L = F := by
  obtain ⟨hext, hextfront⟩ := hK.compl_interior
  have hboundary : frontier (interior K)ᶜ ⊆ interior H := by
    rw [hextfront]
    exact hK.closed.frontier_subset.trans hKH
  have hfront : frontier L = frontier K ∪ (frontier H ∩ (interior K)ᶜ) := by
    rw [hL, Set.frontier_inter_of_frontier_subset_interior hH.closed hext.closed
      hboundary, hextfront]
  have hFH : F ⊆ interior H :=
    hcut.symm.subset.trans (inter_subset_right.trans (hK.closed.frontier_subset.trans hKH))
  exact protected_local_exterior_frontier hcut hFH hfront

end PoincareMT.M76
