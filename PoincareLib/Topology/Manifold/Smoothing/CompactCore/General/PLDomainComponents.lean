import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Regions.Mathlib.ClopenDomainFrontier
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Topology.PLDomainLocalPathConnected
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.General.ProtectedPLIntersection

/-!
# The original PL charts on actual compact-domain components

The relatively open component has one ambient open defining set.
Restricting each original boundary chart to that set preserves its
full halfspace equation and both PL transition directions.
See Hamilton1976 Lemma2 and Wall derivation003, section3.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {P L : Set X}

/-- A closed, relatively open piece retains the original ambient PL
atlas and every boundary halfspace equation. See Wall003, section3. -/
theorem PLDomain.of_relative_clopen_subset (hP : PLDomain e P)
    (hLP : L ⊆ P) (hL : IsClosed L)
    (hopen : IsOpen ((Subtype.val : P → X) ⁻¹' L)) : PLDomain e L := by
  obtain ⟨U, hU, hLU⟩ := Set.exists_open_inter_of_relative_open hLP hopen
  have hfront := Set.frontier_eq_inter_of_eq_inter_open hP.closed hL hU hLU
  refine ⟨hP.cover, hP.compatible, hL, ?_⟩
  intro x hx
  rw [hfront] at hx
  have hxLU : x ∈ P ∩ U := by
    rw [← hLU]
    exact hx.1
  obtain ⟨ell, v, B, hv, hxB, hzero, hBe, hhalf⟩ := hP.halfspace x hx.2
  let H := B.restrOpen U hU
  refine ⟨ell, v, H, hv, ⟨hxB, hxLU.2⟩, hzero, ?_, ?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right B (hBe i) hU
  · intro y hy
    change y ∈ L ↔ 0 ≤ ell (B y)
    rw [hLU]
    exact ⟨fun h => (hhalf y hy.1).mp h.1,
      fun h => ⟨(hhalf y hy.1).mpr h, hy.2⟩⟩

/-- A specified actual component of a compact PL domain is a PL
domain in the same ambient chart family. Its relative openness is
derived from the domain's literal halfspace charts. See Wall003, section3. -/
theorem PLDomain.connectedComponentIn [T2Space X] (hP : PLDomain e P)
    (hPc : IsCompact P) {x : X} (hxP : x ∈ P) :
    PLDomain e (connectedComponentIn P x) := by
  let : LocallyPathConnectedSpace P := hP.locallyPathConnectedSpace
  exact hP.of_relative_clopen_subset (connectedComponentIn_subset P x)
    (Set.isCompact_connectedComponentIn_of_mem hPc hxP).isClosed
    (Set.isOpen_preimage_connectedComponentIn hxP)

end PoincareMT.M76
