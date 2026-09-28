import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneProductCut
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMeridianBand

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

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

def closedStrip : Set W := P.map '' (D2 ×ˢ Icc (-(P.width / 2)) (P.width / 2))

def openStrip : Set W := P.map '' (D2 ×ˢ Ioo (-(P.width / 2)) (P.width / 2))

def endDisks : Set W := P.map '' (D2 ×ˢ ({-(P.width / 2), P.width / 2} : Set ℝ))

def cutCarrier : Set W := complementaryRegion B \ P.openStrip

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
end PoincareConjecture.M76.HamiltonIndexOne
