import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskLowerProducts
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskVertexProducts

/-!
# The exact whole side band read by the vertex extension

Its producer pastes the actual incident edge products and complete
old-frontier product on the same T. The whole ambient rim need not be
the image of this band. See Hudson1969, pp.58--63 and351f.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}
  {C : HamiltonProperDiskCoherentSides T c}

/-- The actual whole base-rim band, retaining all previously built
higher-face products and the entire old-frontier contact. It is an
internal construction from P, not a named geometric input. See351f. -/
structure HamiltonProperDiskVertexBand
    (P : HamiltonProperDiskLowerProducts T C) (p : T.disk.vertices) where
  /-- One total map on the exact base-rim product. -/
  map : E × ℝ → E
  /-- Joint finite PL behavior on the entire closed band. -/
  piecewiseAffine : FinitePiecewiseAffineOn map
    ((T.dualRegionRim {(p : E)} ∩ D) ×ˢ I)
  /-- This includes coincidences between distinct face pieces. -/
  injective : InjOn map ((T.dualRegionRim {(p : E)} ∩ D) ×ˢ I)
  /-- Every full time fiber stays on the actual vertex-block rim. -/
  inside : MapsTo map ((T.dualRegionRim {(p : E)} ∩ D) ×ˢ I)
    (T.dualRegionRim {(p : E)})
  /-- The entire central base rim is fixed. -/
  central : ∀ x ∈ T.dualRegionRim {(p : E)} ∩ D, map (x, 0) = x
  /-- The positive side is exactly positive time. -/
  positive : ∀ x ∈ (T.dualRegionRim {(p : E)} ∩ D) ×ˢ I,
    0 ≤ C.labels.height p (map x) ↔ 0 ≤ x.2
  /-- The negative side is exactly negative time. -/
  negative : ∀ x ∈ (T.dualRegionRim {(p : E)} ∩ D) ×ˢ I,
    C.labels.height p (map x) ≤ 0 ↔ x.2 ≤ 0
  /-- Full physical properness is retained on the band. -/
  proper : ∀ x ∈ (T.dualRegionRim {(p : E)} ∩ D) ×ˢ I,
    map x ∈ frontier R ↔ x.1 ∈ frontier R
  /-- Every actual incident higher-face product is kept pointwise. -/
  keep_face : ∀ s ∈ T.disk.faces, 2 ≤ s.card → (p : E) ∈ s →
    ∀ x ∈ T.diskDualBase s ×ˢ I, map x = P.map s x
  /-- The original frontier portion is covered in its entirety. -/
  frontier_image_subset : (T.vertexBlock p).space ∩ frontier R ⊆
    map '' ((T.dualRegionRim {(p : E)} ∩ D) ×ˢ I)

end PoincareMT.M76.HamiltonIndexOne
