import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalProductCut
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLComposition
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalBallTopology
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.AlexanderBaseProductBall
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallNormalization
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall

/-!
# The complete compression strip as an original PL ball

Normalize the actual disk-times-interval parameter, then compose its
finite PL cube map with the original disk product. The entire lateral
annulus and both cap disks form the marked sphere; the lateral annulus
is exactly the intersection with the old frontier. This constructs the
ball used for a supported compression, before changing the map or
asserting a genus decrease. See Waldhausen 1968, pp. 59--60.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 2 : ℝ)) (1 / 2)
local notation "ends" => ({-(1 / 2 : ℝ), 1 / 2} : Set ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

/-- The entire half-width product is a PL ball with the full lateral
annulus and both complete caps as its specified boundary. -/
theorem exists_closedStrip_ball (P : OriginalDiskProduct e R j) :
    Nonempty (ChartwisePLBall e P.closedStrip
      ((P.map '' (Q ×ˢ I)) ∪ P.endDisks)) := by
  let C := D ×ˢ I
  let B := (Q ×ˢ I) ∪ (D ×ˢ ends)
  have hpair : IsFinitePLBallPair (V2 × ℝ) C B :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
      (isFinitePLBallPair_Icc (show -(1 / 2 : ℝ) < 1 / 2 by norm_num))
  let c : (V2 × ℝ) ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨H, hH, hboundary⟩ := hpair.exists_cube_chart c
  obtain ⟨f, hf, hfeq⟩ := hH.symm
  have hfull : C ⊆ D ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hfi (x : closedBall (0 : V3) 1) : f x = (H.symm x : V2 × ℝ) :=
    (hfeq x).symm
  have hmap : MapsTo f (closedBall (0 : V3) 1) C := by
    intro x hx
    rw [hfi ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  obtain ⟨K, hK, hKs, hfaces⟩ := hf
  have hPL : PolyhedralPLInCharts e (P.map ∘ f) (closedBall (0 : V3) 1) := by
    rw [← hKs]
    exact P.polyhedral.comp_finitePiecewiseAffineOn K hK
      ⟨K, hK, rfl, hfaces⟩ (fun x hx => hfull (hmap (hKs.subset hx)))
  have hPi : InjOn P.map C := P.injective.mono hfull
  let : CompactSpace C := isCompact_iff_compactSpace.mp
    ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc)
  let HC : C ≃ₜ P.map '' C := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn P.map C hPi)
    ((P.polyhedral.continuousOn.mono hfull).domRestrict.subtype_mk _)
  have hBimage : P.map '' B = (P.map '' (Q ×ˢ I)) ∪ P.endDisks := image_union _ _ _
  refine ⟨{
    boundary_subset := hBimage ▸ image_mono hpair.1
    parametrization := H.symm.trans HC
    map := P.map ∘ f
    map_eq := fun x => congrArg P.map (hfi x)
    piecewiseAffine := hPL
    boundary_eq := ?_
  }⟩
  intro x
  change P.map (H.symm x) ∈ (P.map '' (Q ×ˢ I)) ∪ P.endDisks ↔ (x : V3) ∈ sphere 0 1
  rw [← hBimage]
  have hmem : P.map (H.symm x) ∈ P.map '' B ↔ (H.symm x : V2 × ℝ) ∈ B := by
    constructor
    · rintro ⟨y, hy, heq⟩
      exact hPi (hpair.1 hy) (H.symm x).property heq ▸ hy
    · exact fun hx => ⟨H.symm x, hx, rfl⟩
  rw [hmem, hboundary, H.apply_symm_apply, frontier_closedBall _ one_ne_zero]

omit [T2Space X] in
/-- The old frontier meets the whole strip in exactly its entire
lateral annulus. In particular no cap interior is an old boundary mark. -/
theorem closedStrip_inter_frontier (P : OriginalDiskProduct e R j) :
    P.closedStrip ∩ frontier R = P.map '' (Q ×ˢ I) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hfront⟩
    have hzfull : z ∈ D ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact ⟨z, ⟨(P.proper z hzfull).mp hfront, hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hzD : z.1 ∈ D := sphere_subset_closedBall hz.1
    refine ⟨⟨z, ⟨hzD, hz.2⟩, rfl⟩, ?_⟩
    exact (P.proper z ⟨hzD, by linarith [hz.2.1], by linarith [hz.2.2]⟩).mpr hz.1

/-- The marked annulus and caps exhaust the actual ambient frontier
of the constructed compression ball. -/
theorem frontier_closedStrip (P : OriginalDiskProduct e R j) :
    frontier P.closedStrip = (P.map '' (Q ×ˢ I)) ∪ P.endDisks := by
  obtain ⟨b⟩ := P.exists_closedStrip_ball
  exact b.frontier_eq

end PoincareMT.M76.OriginalDiskProduct
