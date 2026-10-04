import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskCoherentSides

/-!
# Exact lower products on the single proper-disk triangulation

The actual triangle and edge constructions supply these complete
carriers, fibers and signs. The vertex extensions consume them without
reselecting either the triangulation or endpoint maps. See Hudson
pp.58--63 and M76 derivation351d.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

/-- The literal disk-side dual carrier on an arbitrary original face.
The original subcomplex intersection identifies it with the disk dual.
See derivation351d. -/
noncomputable def HamiltonProperDiskTriangulation.diskDualBase
    (T : HamiltonProperDiskTriangulation R D b) (s : Finset E) : Set E :=
  T.dualRegion s ∩ D

/-- The actual card-two and card-three products, with full shared
fiber maps and their original geometric images. Its producer is351d;
this record is not a named geometric input. -/
structure HamiltonProperDiskLowerProducts
    (T : HamiltonProperDiskTriangulation R D b) {c : E ≃ᴬ[ℝ] V}
    (C : HamiltonProperDiskCoherentSides T c) where
  /-- One ambient representative for each original higher face. -/
  map : Finset E → E × ℝ → E
  /-- Joint finite PL behavior on the whole closed product. -/
  piecewiseAffine : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    FinitePiecewiseAffineOn (map s) (T.diskDualBase s ×ˢ I)
  /-- Injectivity includes all full endpoint fibers. -/
  injective : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    InjOn (map s) (T.diskDualBase s ×ˢ I)
  /-- The image is the literal region dual block. -/
  image_eq : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    map s '' (T.diskDualBase s ×ˢ I) = T.dualRegion s
  /-- Every point of the central original base stays fixed. -/
  central : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ x ∈ T.diskDualBase s, map s (x, 0) = x
  /-- Physical properness on the complete closed product. -/
  proper : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ x ∈ T.diskDualBase s ×ˢ I,
      map s x ∈ frontier R ↔ x.1 ∈ frontier R
  /-- The complete rim, including every endpoint time. -/
  rim : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ x ∈ T.diskDualBase s ×ˢ I,
      map s x ∈ T.dualRegionRim s ↔
        x.1 ∈ T.dualRegionRim s ∩ D ∨ x.2 ∈ ({-1, 1} : Set ℝ)
  /-- The positive half is independent of the selected vertex chart. -/
  positive : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ x ∈ T.diskDualBase s ×ˢ I,
      0 ≤ C.labels.height p (map s x) ↔ 0 ≤ x.2
  /-- The negative half includes the same entire zero section. -/
  negative : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ x ∈ T.diskDualBase s ×ˢ I,
      C.labels.height p (map s x) ≤ 0 ↔ x.2 ≤ 0
  /-- Every coface product is retained pointwise on its full carrier. -/
  restrict : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ t ∈ T.disk.faces, s ⊆ t → ∀ x ∈ T.diskDualBase t ×ˢ I,
      map s x = map t x
  /-- Complete original shared products agree. -/
  agrees : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ t ∈ T.disk.faces, 2 ≤ t.card →
      ∀ x ∈ (T.diskDualBase s ∩ T.diskDualBase t) ×ˢ I,
        map s x = map t x
  /-- Literal image intersections exclude cross-piece coincidences. -/
  overlap_image : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ t ∈ T.disk.faces, 2 ≤ t.card →
      map s '' ((T.diskDualBase s ∩ T.diskDualBase t) ×ˢ I) =
        T.dualRegion s ∩ T.dualRegion t
  /-- The complete boundary-edge fiber used by the frontier vertex
  product is the literal old-frontier dual interval. -/
  boundary_image : ∀ s ∈ T.disk.faces, s.card = 2 → s ∈ T.boundary.faces →
    (fun t : ℝ => map s (s.centroid ℝ id, t)) '' I =
      T.dualRegion s ∩ frontier R

end PoincareMT.M76.HamiltonIndexOne
