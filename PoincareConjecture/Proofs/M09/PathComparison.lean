import PoincareConjecture.Statements.Ch06.LGeometry








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J}
  {T τmax τ : ℝ} {p q : M}

theorem reducedLength_le_path (hL : LGeodesicTheory F T τmax)
    (hτ : 0 < τ) (hmax : τ ≤ τmax) (c : BackwardTimePath F T 0 τ)
    (hc0 : c.curve 0 = p) (hcτ : c.curve τ = q) :
    reducedLength F T p q τ ≤ backwardLLength F T 0 τ c.curve / (2 * Real.sqrt τ) := by
  obtain ⟨a, ha0, haτ, hmin, hvalue⟩ := hL.reduced_length_attained τ hτ hmax p q
  rw [hvalue]
  exact div_le_div_of_nonneg_right
    (hmin c (hc0.trans ha0.symm) (hcτ.trans haτ.symm))
    (mul_nonneg zero_le_two (Real.sqrt_nonneg τ))

theorem reducedLength_eq_minimizing_path (hL : LGeodesicTheory F T τmax)
    (hτ : 0 < τ) (hmax : τ ≤ τmax) (c : BackwardTimePath F T 0 τ)
    (hc0 : c.curve 0 = p) (hcτ : c.curve τ = q)
    (hc : IsMinimizingBackwardLPath F T 0 τ c) :
    reducedLength F T p q τ = backwardLLength F T 0 τ c.curve / (2 * Real.sqrt τ) := by
  obtain ⟨a, ha0, haτ, hmin, hvalue⟩ := hL.reduced_length_attained τ hτ hmax p q
  have heq : backwardLLength F T 0 τ a.curve = backwardLLength F T 0 τ c.curve :=
    le_antisymm (hmin c (hc0.trans ha0.symm) (hcτ.trans haτ.symm))
      (hc a (ha0.trans hc0.symm) (haτ.trans hcτ.symm))
  exact hvalue.trans (congrArg (fun a : ℝ ↦ a / (2 * Real.sqrt τ)) heq)

end PoincareConjecture.Proofs.M09
