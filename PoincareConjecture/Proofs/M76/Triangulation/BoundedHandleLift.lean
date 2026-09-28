import PoincareConjecture.Proofs.M76.Mathlib.LatticeHomeomorphLift
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinderProduct

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local notation "B" => closedBall (0 : ι → ℝ) 1
local notation "D" => coordinateCylinder
  (Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ))

theorem exists_boundedHandleLift
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (g : (B × ((κ → ℝ) ⧸ L.toAddSubgroup)) ≃ₜ
      (B × ((κ → ℝ) ⧸ L.toAddSubgroup)))
    (H : (ContinuousMap.id (B × ((κ → ℝ) ⧸ L.toAddSubgroup))).HomotopyRel
      ⟨g, g.continuous⟩ ({a : B | ‖(a : ι → ℝ)‖ = 1} ×ˢ univ)) :
    ∃ G : D ≃ₜ D,
      (∀ x, ((coordinateCylinderProduct ι κ (G x)).1,
          QuotientAddGroup.mk (coordinateCylinderProduct ι κ (G x)).2) =
        g ((coordinateCylinderProduct ι κ x).1,
          QuotientAddGroup.mk (coordinateCylinderProduct ι κ x).2)) ∧
      (∀ x : D, (x : (ι ⊕ κ) → ℝ) ∈ frontier D → G x = x) ∧
      ∃ C > 0, ∀ x : D, ‖(G x : (ι ⊕ κ) → ℝ) - x‖ ≤ C := by
  obtain ⟨G, hG, hGfixed, _, C, _, hC⟩ :=
    IsZLattice.exists_bounded_relative_homeomorph_lift L g
      {a : B | ‖(a : ι → ℝ)‖ = 1} H
  let e := coordinateCylinderProduct ι κ
  let G' := (e.trans G).trans e.symm
  have heG (x : D) : e (G' x) = G (e x) := e.apply_symm_apply _
  refine ⟨G', ?_, ?_, max 2 C, lt_max_of_lt_left (by norm_num), ?_⟩
  · intro x
    change ((e (G' x)).1, QuotientAddGroup.mk (e (G' x)).2) =
      g ((e x).1, QuotientAddGroup.mk (e x).2)
    rw [heG]
    exact hG (e x)
  · intro x hx
    apply e.injective
    rw [heG]
    exact hGfixed (e x) (coordinateCylinderProduct_frontier ι κ x hx)
  · exact coordinateCylinderProduct_displacement ι κ G hC

end PoincareConjecture.M76
