import PoincareConjecture.Proofs.M76.Rigidity.OriginalProperDiskTriangulation

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]

structure OriginalDiskProduct
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X) (j : V2 → X) where
  map : V2 × ℝ → X
  polyhedral : PolyhedralPLInCharts e map (D ×ˢ I)
  injective : InjOn map (D ×ˢ I)
  embedding : Topology.IsClosedEmbedding (fun z : (D ×ˢ I : Set (V2 × ℝ)) => map z)
  inside : MapsTo map (D ×ˢ I) R
  central : ∀ z ∈ D, map (z, 0) = j z
  proper : ∀ x ∈ D ×ˢ I, map x ∈ frontier R ↔ x.1 ∈ Q

end PoincareConjecture.M76
