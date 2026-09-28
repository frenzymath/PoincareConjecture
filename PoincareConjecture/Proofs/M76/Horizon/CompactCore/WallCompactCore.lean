import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Spheres.TerminalSphericalFamily
import PoincareConjecture.Proofs.M76.Wall.SingleSphericalFrontier

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

theorem hasWallCompactCore
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)) : HasWallCompactCore e := by
  intro R hR hRconn hB hend A hA hAR
  obtain ⟨n, K, S, hKc, hKconn, hKR, hK, hS, hdisjoint, hSint, hfront, hprotect⟩ :=
    exists_original_terminal_spherical_family e hR hRconn hB hend hA hAR
  obtain ⟨M, T, hMc, _hMconn, _hKM, hMR, hM, hT, hTint, hBT, hfrontM,
    hrelM, hprotectM⟩ :=
    exists_single_spherical_frontier_of_finite_family hR hRconn hend hK hKc hKconn hKR
      (hA.union hB).isClosed (union_subset hAR hR.closed.frontier_subset)
      subset_union_right hprotect S hS hdisjoint hSint hfront
  exact ⟨M, T, hMc, hMR, hM, hTint, hT, hBT, hfrontM, hprotectM, hrelM⟩

end PoincareConjecture.M76
