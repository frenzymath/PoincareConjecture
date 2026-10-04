import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Spheres.TerminalSphericalFamily
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Spheres.SingleSphericalFrontier

/-!
# PL compact cores at simply connected ends

The constructed terminal spherical family and finite-sphere reduction yield
the unchanged Wall compact-core predicate. See Hamilton 1976, Lemma 2 and its
application, pp. 65--66, and the imported Wall009 and Wall016 constructions.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

/-- Wall's compact core, with the entire old frontier protected and exactly
one new embedded PL sphere, constructed from the original hypotheses. -/
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

end PoincareMT.M76
