import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorHigherDerivatives
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSourceWeakJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Metric
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem hasFiniteWeakJet_localized_lowerOrder {K : Set V} (hK : IsClosed K)
    (B : Fin n → 𝓢(V, ℝ)) (C : 𝓢(V, ℝ)) (u : dirichletForm K) {s : ℕ}
    (hu : HasInteriorWeakJets K u (s + 1)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K) :
    HasFiniteWeakJet (schwartzMultiplier χ (dirichletLowerOrder hK B C u : L2)) s := by
  have hfirst (i : Fin n) : HasFiniteWeakJet
      (schwartzMultiplier (schwartzProduct χ (B i)) (dirichletPartial K i u)) s :=
    hu.partial_product (schwartzProduct χ (B i)) hχ.mul_right
      (tsupport_mul_subset_left.trans hχK) i
  have hzero := (hu (schwartzProduct χ C) hχ.mul_right
    (tsupport_mul_subset_left.trans hχK)).mono (Nat.le_succ s)
  have hsum := (HasFiniteWeakJet.sum _ hfirst).add hzero
  simpa only [dirichletLowerOrder_coe, map_add, map_sum,
    localizedDirichletValue, schwartzMultiplier_product] using hsum

theorem hasFiniteWeakJet_localized_vector_lowerOrder {K : Set V} (hK : IsClosed K)
    (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ)) (C : Fin m → Fin m → 𝓢(V, ℝ))
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K)) {s : ℕ}
    (hu : ∀ k, HasInteriorWeakJets K (u k) (s + 1)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K) (k : Fin m) :
    HasFiniteWeakJet (schwartzMultiplier χ (dirichletVectorLowerOrder hK B C u k : L2)) s := by
  have hsum := HasFiniteWeakJet.sum _ (fun i => hasFiniteWeakJet_localized_lowerOrder hK
    (B k i) (C k i) (u i) (hu i) χ hχ hχK)
  simpa only [dirichletVectorLowerOrder_coe, map_sum] using hsum

theorem exists_raw_compact_heat_interior_higherJet
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1)
    (u w : PiLp 2 (fun _ : Fin n => dirichletForm K)) {s : ℕ}
    (hu : ∀ k, HasInteriorWeakJets K (u k) (s + 1))
    (hw : ∀ k, HasInteriorWeakJets K (w k) s)
    (heq : ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) w) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator D hK.isClosed η hη u) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient g η hη) z u)
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (k : Fin n) :
    ∃ q : List (Fin n) → L2, q [] = localizedDirichletValue K χ (u k) ∧
      (∀ i, q [i] = localizedDirichletPartial K χ (u k) i) ∧
        IsWeakSchwartzJet q (s + 2) := by
  let A := rawCutoffPrincipalCoefficient g η hη
  let G : L2 := ((rawLowerFormOperator D hK.isClosed η hη u) k : L2) -
    (dirichletInclusion K (w k) : L2)
  have hG : HasFiniteWeakJet (schwartzMultiplier χ G) s := by
    have hlower := hasFiniteWeakJet_localized_vector_lowerOrder hK.isClosed
      (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) u hu χ hχ hχK k
    simpa only [G, rawLowerFormOperator, map_sub, localizedDirichletValue] using
      hlower.sub (hw k χ hχ hχK)
  have hweak := vector_component_divergence K A
    (rawCutoffPrincipalCoefficient_symmetric g η hη) u
    (rawLowerFormOperator D hK.isClosed η hη u)
    (finiteHilbertMap (dirichletInclusion K) w) heq k
  obtain ⟨δ, hδ, hδK⟩ := hχ.exists_cthickening_subset_open isOpen_interior hχK
  let r : ℝ := δ / 3
  have hr : 0 < r := div_pos hδ (by norm_num)
  have hthick : cthickening (3 * r) (tsupport χ) ⊆ K := by
    have he : 3 * r = δ := by dsimp only [r]; ring
    rw [he]
    exact hδK.trans interior_subset
  obtain ⟨ell, hEll, hell⟩ := exists_rawCutoffPrincipalCoefficient_ellipticity g hK η hη hηK
  obtain ⟨B, hB, hAB⟩ := exists_schwartz_matrix_derivative_bound A
  exact exists_localized_dirichlet_higherJet K A χ hχ hχK (u k) (hu k) G hG hweak
    hr hEll hB (fun x hx => hell x (hthick hx)) hAB

end PoincareConjecture.M35.Uniqueness.Heat
