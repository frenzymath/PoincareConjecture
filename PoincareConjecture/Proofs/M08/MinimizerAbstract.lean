import PoincareConjecture.Proofs.M08.PathBasics
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_isMinOn_of_compact_carrier
    {P : Type*} [TopologicalSpace P] {K : Set P}
    (hK : IsCompact K) (hKne : K.Nonempty) (L : P → ℝ)
    (hL : ContinuousOn L K)
    (hcover : ∀ q : P, ∃ r ∈ K, L r ≤ L q) :
    ∃ p ∈ K, ∀ q : P, L p ≤ L q := by
  obtain ⟨p, hp, hpmin⟩ := hK.exists_isMinOn hKne hL
  refine ⟨p, hp, ?_⟩
  intro q
  obtain ⟨r, hr, hrq⟩ := hcover q
  exact (hpmin hr).trans hrq

theorem exists_minimizingBackwardLPath_of_compact_carrier
    {J : Set ℝ} {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ}
    {K : Set (BackwardTimePath F T τ₁ τ₂)} {p₁ p₂ : M}
    [TopologicalSpace (BackwardTimePath F T τ₁ τ₂)]
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hpairs : ∀ p ∈ K, p.curve τ₁ = p₁ ∧ p.curve τ₂ = p₂)
    (hcover : ∀ q : BackwardTimePath F T τ₁ τ₂,
      q.curve τ₁ = p₁ → q.curve τ₂ = p₂ →
        ∃ r ∈ K,
          backwardLLength F T τ₁ τ₂ r.curve ≤
            backwardLLength F T τ₁ τ₂ q.curve)
    (hL : ContinuousOn
      (fun p : BackwardTimePath F T τ₁ τ₂ ↦
        backwardLLength F T τ₁ τ₂ p.curve) K) :
    ∃ p ∈ K, IsMinimizingBackwardLPath F T τ₁ τ₂ p := by
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hKne hL
  refine ⟨p, hp, ?_⟩
  intro q hleft hright
  have hpairs' := hpairs p hp
  obtain ⟨r, hr, hcost⟩ := hcover q (hleft.trans hpairs'.1)
    (hright.trans hpairs'.2)
  exact (hmin hr).trans hcost

end PoincareConjecture.M08
