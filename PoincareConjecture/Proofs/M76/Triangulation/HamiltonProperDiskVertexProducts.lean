import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskDualSigns
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnmarkedDiskProduct











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}



noncomputable def HamiltonProperDiskTriangulation.diskVertexBlock
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) : Set E :=
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  (T.disk.barycentricDualBlock {(p : E)}).space



structure HamiltonProperDiskVertexProducts
    (T : HamiltonProperDiskTriangulation R D b) where

  map : T.disk.vertices → E × ℝ → E

  piecewiseAffine : ∀ p, FinitePiecewiseAffineOn (map p) (T.diskVertexBlock p ×ˢ I)

  injective : ∀ p, InjOn (map p) (T.diskVertexBlock p ×ˢ I)

  image_eq : ∀ p, map p '' (T.diskVertexBlock p ×ˢ I) = T.dualRegion {(p : E)}

  central : ∀ p x, x ∈ T.diskVertexBlock p → map p (x, 0) = x

  proper : ∀ p x, x ∈ T.diskVertexBlock p ×ˢ I →
    (map p x ∈ frontier R ↔ x.1 ∈ frontier R)

  agrees : ∀ p q x, x ∈ (T.diskVertexBlock p ∩ T.diskVertexBlock q) ×ˢ I →
    map p x = map q x

  overlap_image : ∀ p q,
    map p '' ((T.diskVertexBlock p ∩ T.diskVertexBlock q) ×ˢ I) =
      T.dualRegion {(p : E)} ∩ T.dualRegion {(q : E)}

end PoincareConjecture.M76.HamiltonIndexOne
