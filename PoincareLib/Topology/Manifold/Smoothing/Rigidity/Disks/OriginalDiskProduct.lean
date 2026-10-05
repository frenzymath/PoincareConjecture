import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalProperDiskTriangulation

/-!
# The actual original-atlas product of a proper disk

The record retains the whole closed product, literal original disk
values and exact original-frontier preimage. Its producer follows
in the next module. See Hudson1969, pp.58--63 and rigidity034.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]

/-- A constructed original-chart product on the entire closed
source. No relative openness or lateral marking is included here.
See rigidity034, sections4--5. -/
structure OriginalDiskProduct
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X) (j : V2 → X) where
  map : V2 × ℝ → X
  polyhedral : PolyhedralPLInCharts e map (D ×ˢ I)
  injective : InjOn map (D ×ˢ I)
  embedding : Topology.IsClosedEmbedding (fun z : (D ×ˢ I : Set (V2 × ℝ)) => map z)
  inside : MapsTo map (D ×ˢ I) R
  central : ∀ z ∈ D, map (z, 0) = j z
  proper : ∀ x ∈ D ×ˢ I, map x ∈ frontier R ↔ x.1 ∈ Q

end PoincareMT.M76
