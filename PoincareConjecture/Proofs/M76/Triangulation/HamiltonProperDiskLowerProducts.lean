import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskCoherentSides

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

noncomputable def HamiltonProperDiskTriangulation.diskDualBase
    (T : HamiltonProperDiskTriangulation R D b) (s : Finset E) : Set E :=
  T.dualRegion s ∩ D

structure HamiltonProperDiskLowerProducts
    (T : HamiltonProperDiskTriangulation R D b) {c : E ≃ᴬ[ℝ] V}
    (C : HamiltonProperDiskCoherentSides T c) where

  map : Finset E → E × ℝ → E

  piecewiseAffine : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    FinitePiecewiseAffineOn (map s) (T.diskDualBase s ×ˢ I)

  injective : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    InjOn (map s) (T.diskDualBase s ×ˢ I)

  image_eq : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    map s '' (T.diskDualBase s ×ˢ I) = T.dualRegion s

  central : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ x ∈ T.diskDualBase s, map s (x, 0) = x

  proper : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ x ∈ T.diskDualBase s ×ˢ I,
      map s x ∈ frontier R ↔ x.1 ∈ frontier R

  rim : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ x ∈ T.diskDualBase s ×ˢ I,
      map s x ∈ T.dualRegionRim s ↔
        x.1 ∈ T.dualRegionRim s ∩ D ∨ x.2 ∈ ({-1, 1} : Set ℝ)

  positive : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ x ∈ T.diskDualBase s ×ˢ I,
      0 ≤ C.labels.height p (map s x) ↔ 0 ≤ x.2

  negative : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ x ∈ T.diskDualBase s ×ˢ I,
      C.labels.height p (map s x) ≤ 0 ↔ x.2 ≤ 0

  restrict : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ t ∈ T.disk.faces, s ⊆ t → ∀ x ∈ T.diskDualBase t ×ˢ I,
      map s x = map t x

  agrees : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ t ∈ T.disk.faces, 2 ≤ t.card →
      ∀ x ∈ (T.diskDualBase s ∩ T.diskDualBase t) ×ˢ I,
        map s x = map t x

  overlap_image : ∀ s ∈ T.disk.faces, 2 ≤ s.card →
    ∀ t ∈ T.disk.faces, 2 ≤ t.card →
      map s '' ((T.diskDualBase s ∩ T.diskDualBase t) ×ˢ I) =
        T.dualRegion s ∩ T.dualRegion t

  boundary_image : ∀ s ∈ T.disk.faces, s.card = 2 → s ∈ T.boundary.faces →
    (fun t : ℝ => map s (s.centroid ℝ id, t)) '' I =
      T.dualRegion s ∩ frontier R

end PoincareConjecture.M76.HamiltonIndexOne
