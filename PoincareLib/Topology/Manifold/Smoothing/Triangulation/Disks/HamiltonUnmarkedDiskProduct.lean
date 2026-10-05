import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskTriangulation

/-!
# The actual unmarked product from the common proper-disk blocks

The finite block induction uses one shared triangulation and retains
the original entire disk parameter. A separate relative correction
then replaces its lateral band by the prescribed marked meridian band.
This record contains no openness or terminal-ball supplier.
See Hudson 1969, pp.58--63 and M76 derivation351.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One actual proper disk product on the fixed whole interval. Its
construction consumes the shared `HamiltonProperDiskTriangulation`;
the full original central parameter is retained. The prescribed band
is imposed later by the concrete boundary correction in351. -/
structure HamiltonUnmarkedDiskProduct (R : Set E) {D : Set E} (b : D2 ≃ₜ D) where
  /-- The single ambient representative on the fixed product. -/
  map : (V2 × ℝ) → E
  /-- Joint finite PL behavior on the whole closed product. -/
  piecewiseAffine : FinitePiecewiseAffineOn map (D2 ×ˢ I)
  /-- Injectivity includes both entire endpoint disks. -/
  injective : InjOn map (D2 ×ˢ I)
  /-- The whole product lies in the original region. -/
  inside : MapsTo map (D2 ×ˢ I) R
  /-- Only the full lateral cylinder meets the original frontier. -/
  proper : ∀ x ∈ D2 ×ˢ I, map x ∈ frontier R ↔ x.1 ∈ Q2
  /-- Every original disk value survives, including its whole rim. -/
  central : ∀ x : D2, map ((x : V2), 0) = b x

end PoincareMT.M76.HamiltonIndexOne
