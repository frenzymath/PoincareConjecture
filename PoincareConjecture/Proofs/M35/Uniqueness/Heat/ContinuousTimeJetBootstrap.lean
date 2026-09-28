import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousTimeJetSource
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousEllipticGain









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Metric
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n m : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem continuous_timeJet_elliptic_bootstrap {K : Set V} (hK : IsCompact K)
    (A : ℕ → ι → Fin n → Fin n → 𝓢(V, ℝ))
    (B : ℕ → ι → Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : ℕ → ι → Fin m → Fin m → 𝓢(V, ℝ))
    (u : ℕ → ι → PiLp 2 (fun _ : Fin m => dirichletForm K))
    (hu : ∀ j k, Continuous (fun t => u j t k))
    (hA : ∀ r i j w,
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A r t i j))))
    (hB : ∀ r i j k w,
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (B r t i j k))))
    (hC : ∀ r i j w,
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (C r t i j))))
    (hsymm : ∀ t i j x, A 0 t i j x = A 0 t j i x)
    {ell D : ℝ} (hell : 0 < ell) (hD : 0 ≤ D)
    (hEll : ∀ t, ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 t i j x * ξ i * ξ j)
    (hAD : ∀ t i j x, ‖fderiv ℝ (A 0 t i j) x‖ ≤ D)
    (heq : ∀ l t, ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (u (l + 1) t)) =
      ∑ p ∈ Finset.antidiagonal l, (l.choose p.1 : ℝ) *
        (inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (dirichletVectorLowerOrder hK.isClosed (B p.1 t) (C p.1 t) (u p.2 t)) -
            principalVectorEnergy K (A p.1 t) z (u p.2 t))) :
    ∀ s j k, HasContinuousInteriorJets K (fun t => u j t k) (s + 1) := by
  intro s
  induction s with
  | zero => exact fun j k => hasContinuousInteriorJets_one _ (hu j k)
  | succ s ih =>
    intro j
    induction j using Nat.strong_induction_on with
    | h j hj =>
      intro k χ hχ hχK
      obtain ⟨G, hG, he⟩ := exists_continuous_timeJet_cutoff_source hK.isClosed A B C u j s
        (fun r i j w _ => hA r i j w) (fun r i j k w _ => hB r i j k w)
        (fun r i j w _ => hC r i j w) ih hj (heq j) χ hχ hχK k
      have htest (t : ι) (φ : 𝓢(V, ℝ)) : principalEnergy K (A 0 t) (u j t k)
          (intoDirichletForm K (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) =
            inner ℝ (G t) (φ.toLp 2 volume) :=
        (principalEnergy_symmetric K (A 0 t) (hsymm t) _ _).trans (he t φ)
      obtain ⟨δ, hδ, hδK⟩ := hχ.exists_cthickening_subset_open isOpen_interior hχK
      let r : ℝ := δ / 3
      have hr : 0 < r := div_pos hδ (by norm_num)
      have hthick : cthickening (3 * r) (tsupport χ) ⊆ K := by
        have he : 3 * r = δ := by dsimp only [r]; ring
        rw [he]
        exact hδK.trans interior_subset
      exact hasContinuousWeakJet_of_cutoff_tests K (A 0) (fun i j w _ => hA 0 i j w)
        χ hχ hχK (fun t => u j t k) (ih j k) G hG htest hr hell hD
        (fun t x hx => hEll t x (hthick hx)) hAD

end PoincareConjecture.M35.Uniqueness.Heat
