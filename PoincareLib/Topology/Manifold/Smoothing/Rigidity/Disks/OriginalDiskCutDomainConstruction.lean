import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Levels.OriginalCutDomain
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalDiskCutConstruction

/-!
# The full original cut domain from a given proper PL disk

Construct the small product and its entire open middle internally,
then every halfspace chart of its actual physical cut. The whole
frontier and both cap marks are retained. See rigidity040, section5.
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

/-- The actual original disk constructs a small physical cut that
is a PL domain in the unchanged atlas. No product, cap chart, side,
cut-domain or ball supplier occurs. See rigidity040. -/
theorem exists_original_disk_cut_domain
    (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    {U : Set X} (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ P : OriginalDiskProduct e R j,
      MapsTo P.map (D ×ˢ I) U ∧
      IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip) ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧
      interior P.cutCarrier = interior R \ P.closedStrip ∧
      frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = R ∧
      (interior P.cutCarrier).Nonempty := by
  obtain ⟨P, hsmall, hopen, hgeometry⟩ :=
    exists_original_disk_cut hR he hj hemb hDR hproper hU hDU
  exact ⟨P, hsmall, hopen, P.plDomain_cut hR he hopen, hgeometry⟩

end PoincareMT.M76
