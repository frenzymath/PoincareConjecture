import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorFiniteJets









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

theorem hasFiniteWeakJet_localizedDivergenceSource (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : dirichletForm K) {s : ℕ} (hu : HasInteriorWeakJets K u (s + 1)) (G : L2)
    (hG : HasFiniteWeakJet (schwartzMultiplier χ G) s) :
    HasFiniteWeakJet (localizedDivergenceSource K A χ u G) s := by
  have hχd (i : Fin n) : HasCompactSupport
      ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) :=
    hχ.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _)
  have hχdK (i : Fin n) :
      tsupport ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) ⊆ interior K :=
    (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hχK
  let term : Fin n → Fin n → L2 := fun i j =>
    schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} χ)
      (schwartzMultiplier (A i j) (dirichletPartial K i u)) +
    (schwartzMultiplier (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ))
      (dirichletPartial K j u) +
    schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
      (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ)))
      (dirichletInclusion K u : L2))
  have hterm (i j : Fin n) : HasFiniteWeakJet (term i j) s := by
    have h₁ := hu.partial_product
      (schwartzProduct (∂_{EuclideanSpace.single j (1 : ℝ)} χ) (A i j))
      (hχd j).mul_right (tsupport_mul_subset_left.trans (hχdK j)) i
    rw [schwartzMultiplier_product] at h₁
    let a := schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ)
    have ha : HasCompactSupport a := (hχd i).mul_left
    have haK : tsupport a ⊆ interior K := tsupport_mul_subset_right.trans (hχdK i)
    have h₂ := hu.partial_product a ha haK j
    have had : HasCompactSupport
        ((∂_{EuclideanSpace.single j (1 : ℝ)} a : 𝓢(V, ℝ)) : V → ℝ) :=
      ha.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _)
    have hadK : tsupport ((∂_{EuclideanSpace.single j (1 : ℝ)} a : 𝓢(V, ℝ)) : V → ℝ) ⊆
        interior K := (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans haK
    have h₃ := (hu (∂_{EuclideanSpace.single j (1 : ℝ)} a) had hadK).mono (Nat.le_succ s)
    exact h₁.add (h₂.add h₃)
  exact hG.sub (HasFiniteWeakJet.sum (fun i => ∑ j, term i j)
    (fun i => HasFiniteWeakJet.sum (term i) (hterm i)))

theorem exists_localized_dirichlet_higherJet (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : dirichletForm K) {s : ℕ} (hu : HasInteriorWeakJets K u (s + 1)) (G : L2)
    (hG : HasFiniteWeakJet (schwartzMultiplier χ G) s)
    (heq : ∀ φ : supportedTests K, principalEnergy K A u (intoDirichletForm K φ) =
      inner ℝ G ((φ : 𝓢(V, ℝ)).toLp 2 volume))
    {r ell B : ℝ} (hr : 0 < r) (hEll : 0 < ell) (hB : 0 ≤ B)
    (hell : ∀ x ∈ cthickening (3 * r) (tsupport χ), ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B) :
    ∃ q : List (Fin n) → L2, q [] = localizedDirichletValue K χ u ∧
      (∀ i, q [i] = localizedDirichletPartial K χ u i) ∧ IsWeakSchwartzJet q (s + 2) := by
  obtain ⟨source, hsource0, hsource⟩ :=
    hasFiniteWeakJet_localizedDivergenceSource K A χ hχ hχK u hu G hG
  have hdiv : DivergenceEquation A (localizedDirichletPartial K χ u) (source [])
      (cthickening (3 * r) (tsupport χ)) := by
    rw [hsource0]
    exact fun φ _ _ => localized_dirichlet_divergence K A χ
      (hχK.trans interior_subset) u G heq φ
  obtain ⟨q, hq0, hq1, hq, _⟩ := exists_finite_weakJet_of_divergence
    (localizedDirichletValue K χ u) (localizedDirichletPartial K χ u)
    (localizedDirichletPartial_weak K χ u) hχ (localizedDirichletValue_ae_support K χ u)
    A hr hEll hB hell hAB source hdiv s hsource
  exact ⟨q, hq0, hq1, hq⟩

end PoincareConjecture.M35.Uniqueness.Heat
