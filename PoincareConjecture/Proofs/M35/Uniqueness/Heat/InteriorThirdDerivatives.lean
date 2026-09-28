import PoincareConjecture.Proofs.M35.Uniqueness.Heat.LocalizedSourceWeakJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Metric
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_localized_dirichlet_thirdJet (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : dirichletForm K) (hu : HasInteriorSecondDerivatives K u) (G : L2)
    (hG : ∀ i : Fin n, ∃ d : L2, HasWeakSchwartzDerivative
      (schwartzMultiplier χ G) d (EuclideanSpace.single i (1 : ℝ)))
    (heq : ∀ φ : supportedTests K, principalEnergy K A u (intoDirichletForm K φ) =
      inner ℝ G ((φ : 𝓢(V, ℝ)).toLp 2 volume))
    {r ell B : ℝ} (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (3 * r) (tsupport χ), ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B) :
    ∃ q : List (Fin n) → L2, q [] = localizedDirichletValue K χ u ∧
      (∀ i, q [i] = localizedDirichletPartial K χ u i) ∧ IsWeakSchwartzJet q 3 := by
  choose Gk hGk using hG
  choose d hd using fun i => exists_weak_derivative_localized_source K A χ hχ hχK
    u hu G (Gk i) i (hGk i)
  let source : List (Fin n) → L2
    | [] => localizedDivergenceSource K A χ u G
    | i :: _ => d i
  have hsource : IsWeakSchwartzJet source 1 := by
    intro w hw i
    have he : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst w
    exact hd i
  have hdiv : DivergenceEquation A (localizedDirichletPartial K χ u) (source [])
      (cthickening (3 * r) (tsupport χ)) :=
    fun φ _ _ => localized_dirichlet_divergence K A χ (hχK.trans interior_subset) u G heq φ
  obtain ⟨q, hq0, hq1, hq, _⟩ := exists_finite_weakJet_of_divergence
    (localizedDirichletValue K χ u) (localizedDirichletPartial K χ u)
    (localizedDirichletPartial_weak K χ u) hχ (localizedDirichletValue_ae_support K χ u)
    A hr hEll hB hell hAB source hdiv 1 hsource
  exact ⟨q, hq0, hq1, hq⟩

end PoincareConjecture.M35.Uniqueness.Heat
