import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CutoffPrincipalSource
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorHigherDerivatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Metric
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem localized_divergence_of_cutoff_tests (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (χ : 𝓢(V, ℝ)) (hχK : tsupport χ ⊆ K)
    (u : dirichletForm K) (G : L2)
    (heq : ∀ φ : 𝓢(V, ℝ), principalEnergy K A u
      (intoDirichletForm K (cutoffSupportedTest K χ hχK φ)) = inner ℝ G (φ.toLp 2 volume)) :
    ∀ φ : 𝓢(V, ℝ),
      (∑ i, ∑ j, inner ℝ (schwartzMultiplier (A i j) (localizedDirichletPartial K χ u i))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume)) =
          inner ℝ (G + localizedDivergenceSource K A χ u 0) (φ.toLp 2 volume) := by
  intro φ
  have hmain := heq φ
  simp only [principalEnergy, dirichletPartial_into, cutoffSupportedTest,
    lineDeriv_schwartzProduct_toLp, inner_add_right, Finset.sum_add_distrib] at hmain
  have hcut (i j : Fin n) := (dirichletPartial_weak K u j).mul _ _ _
    (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ)) φ
  have hcutSum := congrArg (fun f : Fin n → Fin n → ℝ => ∑ i, ∑ j, f i j)
    (funext (fun i => funext (fun j => hcut i j)))
  simp only [inner_add_left, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    schwartzMultiplier_product] at hcutSum
  simp only [localizedDirichletPartial, map_add, inner_add_left, Finset.sum_add_distrib,
    localizedDivergenceSource, map_zero, zero_sub, inner_neg_left, sum_inner]
  simp_rw [schwartzMultiplier_selfAdjoint] at hmain
  have hcomm (i j : Fin n) :
      inner ℝ (schwartzMultiplier (A i j) (schwartzMultiplier χ (dirichletPartial K i u)))
        ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume) =
      inner ℝ (dirichletPartial K i u) (schwartzMultiplier (A i j)
        (schwartzMultiplier χ ((∂_{EuclideanSpace.single j (1 : ℝ)} φ).toLp 2 volume))) := by
    rw [schwartzMultiplier_commute, schwartzMultiplier_selfAdjoint,
      schwartzMultiplier_selfAdjoint]
  simp_rw [hcomm]
  simp only [schwartzMultiplier_product] at hcutSum ⊢
  have hcross (i j : Fin n) :
      inner ℝ (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} χ)
        (schwartzMultiplier (A i j) (dirichletPartial K i u))) (φ.toLp 2 volume) =
      inner ℝ (dirichletPartial K i u) (schwartzMultiplier (A i j)
        (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} χ) (φ.toLp 2 volume))) := by
    rw [schwartzMultiplier_selfAdjoint, schwartzMultiplier_selfAdjoint]
  simp_rw [hcross]
  linarith only [hmain, hcutSum]

theorem exists_localized_jet_of_cutoff_tests (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : dirichletForm K) {s : ℕ} (hu : HasInteriorWeakJets K u (s + 1)) (G : L2)
    (hG : HasFiniteWeakJet G s)
    (heq : ∀ φ : 𝓢(V, ℝ), principalEnergy K A u
      (intoDirichletForm K (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) =
        inner ℝ G (φ.toLp 2 volume))
    {r ell B : ℝ} (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (3 * r) (tsupport χ), ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B) :
    HasFiniteWeakJet (localizedDirichletValue K χ u) (s + 2) := by
  have hzero : HasFiniteWeakJet (schwartzMultiplier χ (0 : L2)) s := by
    simpa only [map_zero] using HasFiniteWeakJet.zero (n := n) s
  have hsource : HasFiniteWeakJet (G + localizedDivergenceSource K A χ u 0) s :=
    hG.add (hasFiniteWeakJet_localizedDivergenceSource K A χ hχ hχK u hu 0 hzero)
  obtain ⟨source, hsource0, hsource⟩ := hsource
  have hdiv : DivergenceEquation A (localizedDirichletPartial K χ u) (source [])
      (cthickening (3 * r) (tsupport χ)) := by
    rw [hsource0]
    exact fun φ _ _ => localized_divergence_of_cutoff_tests K A χ
      (hχK.trans interior_subset) u G heq φ
  obtain ⟨q, hq0, _, hq, _⟩ := exists_finite_weakJet_of_divergence
    (localizedDirichletValue K χ u) (localizedDirichletPartial K χ u)
    (localizedDirichletPartial_weak K χ u) hχ (localizedDirichletValue_ae_support K χ u)
    A hr hEll hB hell hAB source hdiv s hsource
  exact ⟨q, hq0, hq⟩

end PoincareConjecture.M35.Uniqueness.Heat
