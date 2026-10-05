import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalBallTopology
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalProductCut
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.PlanarRegionSideTransport
import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual irreducible filling avoids the removed disk strip

The complete original strip is connected. Its literal old-frontier
point is outside the filling, while the entire filling frontier lies
in the cut interior. Constant-side transport excludes the whole strip.
The actual cap supplies a second old-frontier witness. See046.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

/-- The whole removed middle strip is connected and nonempty,
including its full lateral boundary. See046, section1. -/
theorem isConnected_openStrip (P : OriginalDiskProduct e R j) :
    IsConnected P.openStrip := by
  apply ((isConnected_closedBall (x := (0 : V2)) zero_le_one).prod
    (isConnected_Ioo (show -(1 / 2 : ℝ) < 1 / 2 by norm_num))).image P.map
  apply P.polyhedral.continuousOn.mono
  intro z hz
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

/-- The literal central rim point is on the old frontier inside
the removed strip; the literal positive cap rim is also on that old
frontier. Both use the same original product. See046, sections1--2. -/
theorem exists_old_frontier_witnesses (P : OriginalDiskProduct e R j) :
    (P.openStrip ∩ frontier R).Nonempty ∧ (P.endDisks ∩ frontier R).Nonempty := by
  let z : V2 := fun _ => 1
  have hzQ : z ∈ Q := by simp [z]
  have hzD : z ∈ D := sphere_subset_closedBall hzQ
  constructor
  · refine ⟨P.map (z, 0), ⟨(z, 0), ⟨hzD, by norm_num⟩, rfl⟩, ?_⟩
    exact (P.proper (z, 0) ⟨hzD, by norm_num⟩).mpr hzQ
  · refine ⟨P.map (z, 1 / 2), ⟨(z, 1 / 2), ⟨hzD, by simp⟩, rfl⟩, ?_⟩
    exact (P.proper (z, 1 / 2) ⟨hzD, by norm_num⟩).mpr hzQ

/-- The same actual ball whose whole boundary lies in the cut
interior avoids the full removed original disk strip. See046, section1. -/
theorem ball_subset_cut [T2Space X] (P : OriginalDiskProduct e R j)
    {B S : Set X} (b : ChartwisePLBall e B S) (hBR : B ⊆ R)
    (hSK : S ⊆ interior P.cutCarrier) : B ⊆ P.cutCarrier := by
  have hKR : P.cutCarrier ⊆ R := sdiff_subset
  have hBint : B ⊆ interior R := b.subset_interior hBR (hSK.trans (interior_mono hKR))
  have havoid : Disjoint P.openStrip (frontier B) := by
    rw [b.frontier_eq]
    exact disjoint_left.mpr (fun x hxW hxS => (interior_subset (hSK hxS)).2 hxW)
  obtain ⟨x, hxW, hxR⟩ := P.exists_old_frontier_witnesses.1
  have hxB : x ∉ B := fun h => hxR.2 (hBint h)
  intro y hyB
  refine ⟨hBR hyB, ?_⟩
  intro hyW
  exact hxB ((P.isConnected_openStrip.isPreconnected.mem_iff_of_disjoint_frontier
    havoid hxW hyW).mpr hyB)

end PoincareMT.M76.OriginalDiskProduct
