import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalProductCut
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalSmallDiskProduct

/-!
# Construct the physical cut from the actual original proper disk

The retained original parameter supplies the product, its entire
relative-open middle and all cut geometry. No neighborhood, cut-ball
or new disk premise is supplied. See rigidity036, section4.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

/-- A given original proper PL disk constructs its small physical
cut, entire frontier and both end disks, with an original ambient
interior point. This does not assert that the cut is a ball. See036. -/
theorem exists_original_disk_cut
    (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    {U : Set X} (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ P : OriginalDiskProduct e R j,
      MapsTo P.map (D ×ˢ I) U ∧
      IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip) ∧
      IsCompact P.cutCarrier ∧
      interior P.cutCarrier = interior R \ P.closedStrip ∧
      frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = R ∧
      (interior P.cutCarrier).Nonempty := by
  obtain ⟨P, hP, hopen⟩ := exists_small_original_disk_product hR he hj hemb hDR hproper hU hDU
  have hstrip : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip) :=
    (hopen (1 / 2) (by norm_num) (by norm_num)).1
  exact ⟨P, hP, hstrip, P.cut_geometry hR hstrip⟩

end PoincareMT.M76
