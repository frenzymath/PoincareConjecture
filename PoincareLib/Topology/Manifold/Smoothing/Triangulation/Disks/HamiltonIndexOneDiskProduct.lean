import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonIndexOneProductCut
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonIndexOneMeridianBand

/-!
# The marked product consumed by the index-one physical cut

This record contains exactly the embedded strip, its boundary incidence
and the already fixed meridian band in the literal complementary region.
It makes no disk-neighborhood existence assertion. See Hamilton 1976,
p.67 and M76 derivations351 and354.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

/-- Only the geometric data read by the marked half-width cut and its
two region-ball constructions. The disk from the named Dehn input is
used to construct this record; its parametrization is not an additional
field of the consumer. See Hamilton p.67 and derivations351/354. -/
structure HamiltonMarkedDiskProduct {B : Set W}
    (e : frontier squareShell ≃ₜ frontier (complementaryRegion B)) where
  width : ℝ
  width_pos : 0 < width
  width_le : width ≤ 1 / 4
  map : (V2 × ℝ) → W
  piecewiseAffine : FinitePiecewiseAffineOn map (D2 ×ˢ Icc (-width) width)
  injective : InjOn map (D2 ×ˢ Icc (-width) width)
  inside : MapsTo map (D2 ×ˢ Icc (-width) width) (complementaryRegion B)
  proper : ∀ x ∈ D2 ×ˢ Icc (-width) width,
    map x ∈ frontier (complementaryRegion B) ↔ x.1 ∈ Q2
  lateral : ∀ (x : Q2) (t : ℝ), t ∈ Icc (-width) width →
    ∀ hx : standardMeridianBandMap ((x : V2), t) ∈ frontier squareShell,
      map ((x : V2), t) = e ⟨standardMeridianBandMap ((x : V2), t), hx⟩
  open_strip : IsOpen ((Subtype.val : complementaryRegion B → W) ⁻¹'
    (map '' (D2 ×ˢ Ioo (-width) width)))

namespace HamiltonMarkedDiskProduct

variable {B : Set W} {e : frontier squareShell ≃ₜ frontier (complementaryRegion B)}
  (P : HamiltonMarkedDiskProduct e)

/-- The physical closed product used for the cut. -/
def closedStrip : Set W := P.map '' (D2 ×ˢ Icc (-(P.width / 2)) (P.width / 2))

/-- The relatively open strip removed by the cut, including its lateral band. -/
def openStrip : Set W := P.map '' (D2 ×ˢ Ioo (-(P.width / 2)) (P.width / 2))

/-- Both complete endpoint disks, with the same product parametrization. -/
def endDisks : Set W := P.map '' (D2 ×ˢ ({-(P.width / 2), P.width / 2} : Set ℝ))

/-- The actual closed subset obtained by removing the half-width strip. -/
def cutCarrier : Set W := complementaryRegion B \ P.openStrip

/-- The narrow product record supplies all of the physical cut's
topology, including its entire frontier and a nonempty ambient interior.
No cut ball or connectedness is assumed. See derivation354. -/
theorem cut_geometry (hR : IsCompact (complementaryRegion B)) :
    IsCompact P.cutCarrier ∧
      interior P.cutCarrier = interior (complementaryRegion B) \ P.closedStrip ∧
      frontier P.cutCarrier = (frontier (complementaryRegion B) \ P.openStrip) ∪ P.endDisks ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = complementaryRegion B ∧
      (interior P.cutCarrier).Nonempty := by
  obtain ⟨hc, hi, hf, hmeet, hcover, hne⟩ := finitePL_proper_product_cut
    (by simp [Module.finrank_prod] : Module.finrank ℝ W = 3)
    hR.isClosed P.map P.width_pos P.piecewiseAffine P.injective P.inside P.open_strip
  exact ⟨hR.of_isClosed_subset hc sdiff_subset, hi, hf, hmeet, hcover, hne⟩

end HamiltonMarkedDiskProduct
end PoincareMT.M76.HamiltonIndexOne
