import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskTriangulation











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





structure HamiltonUnmarkedDiskProduct (R : Set E) {D : Set E} (b : D2 ≃ₜ D) where

  map : (V2 × ℝ) → E

  piecewiseAffine : FinitePiecewiseAffineOn map (D2 ×ˢ I)

  injective : InjOn map (D2 ×ˢ I)

  inside : MapsTo map (D2 ×ˢ I) R

  proper : ∀ x ∈ D2 ×ˢ I, map x ∈ frontier R ↔ x.1 ∈ Q2

  central : ∀ x : D2, map ((x : V2), 0) = b x

end PoincareConjecture.M76.HamiltonIndexOne
