import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimCircles
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_boundaryCircle_of_mem_rim
    (phi : C(H, H)) (theta : C) (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {x : X} (hx : x ∈ sourceSurface phi theta ∩ frontier R) :
    ∃ side c, (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
      (originalIntervalEndpoint_norm side) c : X) = x := by
  let z : ↥(sourceSurface phi theta ∩ frontier R) := ⟨x, hx⟩
  have hz : z ∈ ⋃ side, sourceRimCircle phi theta F0 (originalIntervalEndpoint side) := by
    rw [sourceRimCircle_two_cover]
    trivial
  obtain ⟨side, hside⟩ := mem_iUnion.mp hz
  obtain ⟨c, hc⟩ := (sourceRimCircleCoordinates phi theta F0
    (originalIntervalEndpoint side) (originalIntervalEndpoint_norm side)).surjective ⟨z, hside⟩
  exact ⟨side, c, congrArg (fun y => (y.val : X)) hc⟩

theorem annulus_original_boundary_iff
    (phi : C(H, H)) (theta : C) (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {S : Set X} (hS : S ⊆ sourceSurface phi theta) (A : Ann ≃ₜ S)
    (scale : C32 ≃ₜ C)
    (hmark : ∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
      (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) (scale z) : X)) (x : Ann) :
    (A x : X) ∈ frontier R ↔ depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1 := by
  constructor
  · intro hx
    obtain ⟨side, c, hc⟩ := exists_original_boundaryCircle_of_mem_rim phi theta F0
      ⟨hS (A x).property, hx⟩
    have hh : A (Dehn.annulusRimPoint side (scale.symm c)) = A x := by
      apply Subtype.ext
      rw [hmark, scale.apply_symm_apply]
      exact hc
    rw [← A.injective hh, Dehn.depth_annulusRimPoint]
    cases side <;> simp
  · intro hx
    obtain ⟨side, hs⟩ : ∃ side : Bool, depth 8 (x : ℝ × ℝ) = if side then 1 else -1 := by
      rcases hx with hx | hx
      · exact ⟨false, hx⟩
      · exact ⟨true, hx⟩
    obtain ⟨z, rfl⟩ := (Dehn.range_annulusRimPoint side).symm.subset hs
    rw [hmark]
    exact sourceBoundaryCircle_mem_frontier phi theta F0 _ _ _

end PoincareConjecture.M76.HamiltonIntervalTorus
