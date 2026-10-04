import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskDualSigns
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonUnmarkedDiskProduct

/-!
# The exact output of finite vertex-product extension

The actual source and target dual blocks come from the single shared
triangulation. All overlap equations retain their complete geometric
carriers. This internal record is constructed by the descending block
extension and consumed by finite gluing. See Hudson 1969, pp.58--63
and M76 derivations351 and358.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

/-- The literal disk-side vertex dual block of the shared complex.
See Hudson pp.58--63 and derivation358. -/
noncomputable def HamiltonProperDiskTriangulation.diskVertexBlock
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) : Set E :=
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  (T.disk.barycentricDualBlock {(p : E)}).space

/-- Exact finite vertex extension data. The constructor is an internal
obligation of351, not an external geometric predicate. See358. -/
structure HamiltonProperDiskVertexProducts
    (T : HamiltonProperDiskTriangulation R D b) where
  /-- One total representative per actual original disk vertex. -/
  map : T.disk.vertices → E × ℝ → E
  /-- Joint finite PL behavior on each entire closed product. -/
  piecewiseAffine : ∀ p, FinitePiecewiseAffineOn (map p) (T.diskVertexBlock p ×ˢ I)
  /-- Injectivity retains the whole endpoint disks. -/
  injective : ∀ p, InjOn (map p) (T.diskVertexBlock p ×ˢ I)
  /-- The target is the same actual ambient dual block in R. -/
  image_eq : ∀ p, map p '' (T.diskVertexBlock p ×ˢ I) = T.dualRegion {(p : E)}
  /-- Every central disk point retains its original value. -/
  central : ∀ p x, x ∈ T.diskVertexBlock p → map p (x, 0) = x
  /-- Actual frontier incidence on the complete product. -/
  proper : ∀ p x, x ∈ T.diskVertexBlock p ×ˢ I →
    (map p x ∈ frontier R ↔ x.1 ∈ frontier R)
  /-- Pointwise agreement on every full closed overlap. -/
  agrees : ∀ p q x, x ∈ (T.diskVertexBlock p ∩ T.diskVertexBlock q) ×ˢ I →
    map p x = map q x
  /-- Exact overlap images exclude cross-piece coincidences. -/
  overlap_image : ∀ p q,
    map p '' ((T.diskVertexBlock p ∩ T.diskVertexBlock q) ×ˢ I) =
      T.dualRegion {(p : E)} ∩ T.dualRegion {(q : E)}

end PoincareMT.M76.HamiltonIndexOne
