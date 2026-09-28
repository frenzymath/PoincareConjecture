import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeJetSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Metric
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open DeTurckGeneratorRegularityNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem timeJet_elliptic_bootstrap {K : Set V} (hK : IsCompact K)
    (A : ℕ → Fin n → Fin n → 𝓢(V, ℝ))
    (B : ℕ → Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : ℕ → Fin m → Fin m → 𝓢(V, ℝ))
    (u : ℕ → PiLp 2 (fun _ : Fin m => dirichletForm K))
    (hA : ∀ i j x, A 0 i j x = A 0 j i x)
    {ell : ℝ} (hell : 0 < ell)
    (hEll : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j)
    (heq : ∀ l, ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (u (l + 1))) =
      ∑ p ∈ Finset.antidiagonal l, (l.choose p.1 : ℝ) *
        (inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (dirichletVectorLowerOrder hK.isClosed (B p.1) (C p.1) (u p.2)) -
            principalVectorEnergy K (A p.1) z (u p.2))) :
    ∀ s j k, HasInteriorWeakJets K (u j k) (s + 1) := by
  intro s
  induction s with
  | zero => exact fun j k => hasInteriorWeakJets_one K (u j k)
  | succ s ih =>
    intro j
    induction j using Nat.strong_induction_on with
    | h j hj =>
      intro k χ hχ hχK
      obtain ⟨G, hG, he⟩ := exists_timeJet_cutoff_source hK.isClosed A B C u j s
        ih hj (heq j) χ hχ hχK k
      have htest (φ : 𝓢(V, ℝ)) : principalEnergy K (A 0) (u j k)
          (intoDirichletForm K (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) =
            inner ℝ G (φ.toLp 2 volume) :=
        (principalEnergy_symmetric K (A 0) hA _ _).trans (he φ)
      obtain ⟨δ, hδ, hδK⟩ := hχ.exists_cthickening_subset_open isOpen_interior hχK
      let r : ℝ := δ / 3
      have hr : 0 < r := div_pos hδ (by norm_num)
      have hthick : cthickening (3 * r) (tsupport χ) ⊆ K := by
        have he : 3 * r = δ := by dsimp only [r]; ring
        rw [he]
        exact hδK.trans interior_subset
      obtain ⟨M, hM, hAM⟩ := exists_schwartz_matrix_derivative_bound (A 0)
      exact exists_localized_jet_of_cutoff_tests K (A 0) χ hχ hχK (u j k) (ih j k) G hG htest
        hr hell hM (fun x hx => hEll x (hthick hx)) hAM

end PoincareConjecture.M35.Uniqueness.Heat
