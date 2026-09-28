import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorThirdDerivatives
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSourceWeakJet

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

theorem exists_raw_compact_heat_interior_thirdJet
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1)
    (u w : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (heq : ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) w) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator D hK.isClosed η hη u) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient g η hη) z u)
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (k : Fin n) :
    ∃ q : List (Fin n) → L2, q [] = localizedDirichletValue K χ (u k) ∧
      (∀ i, q [i] = localizedDirichletPartial K χ (u k) i) ∧ IsWeakSchwartzJet q 3 := by
  let Z := finiteHilbertMap (dirichletInclusion K) w
  have hu := raw_compact_heat_hasInteriorSecondDerivatives D hK η hη hηK u Z heq
  let A := rawCutoffPrincipalCoefficient g η hη
  let G : L2 := ((rawLowerFormOperator D hK.isClosed η hη u) k : L2) -
    (dirichletInclusion K (w k) : L2)
  have hG := exists_weak_derivative_raw_source D hK.isClosed η hη u w hu χ hχ hχK k
  have hweak := vector_component_divergence K A
    (rawCutoffPrincipalCoefficient_symmetric g η hη) u
    (rawLowerFormOperator D hK.isClosed η hη u) Z heq k
  obtain ⟨δ, hδ, hδK⟩ := hχ.exists_cthickening_subset_open isOpen_interior hχK
  let r : ℝ := δ / 3
  have hr : 0 < r := div_pos hδ (by norm_num)
  have hthick : cthickening (3 * r) (tsupport χ) ⊆ K := by
    have he : 3 * r = δ := by dsimp only [r]; ring
    rw [he]
    exact hδK.trans interior_subset
  obtain ⟨ell, hEll, hell⟩ := exists_rawCutoffPrincipalCoefficient_ellipticity g hK η hη hηK
  obtain ⟨B, hB, hAB⟩ := exists_schwartz_matrix_derivative_bound A
  exact exists_localized_dirichlet_thirdJet K A χ hχ hχK (u k) (hu k) G hG hweak
    hr hEll hB (fun x hx => hell x (hthick hx)) hAB

end PoincareConjecture.M35.Uniqueness.Heat
