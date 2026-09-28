import PoincareConjecture.Proofs.M34.Mathlib.InverseBilinearCoercivity
import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergyBackground










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem exists_uniform_canonicalDomain_principal_bounds
    (n : ℕ) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ lambda C : ℝ, 0 < lambda ∧ 1 ≤ C ∧
      ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
        letI := hNE
        letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
        letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
        ∀ (g : RiemannianMetric n U) (_D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
          let B := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
          (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B x‖ ≤ M) →
          (∀ v, a * ‖v‖ ^ 2 ≤ B x v v) →
          let A := fun i j => EuclideanSpace.proj i ((B x).inverse (EuclideanSpace.proj j))
          (∀ i j : Fin n, |A i j| ≤ C) ∧
          (∀ z : Fin n → ℝ, lambda * (∑ i, z i ^ 2) ≤
            ∑ i, ∑ j, A i j * z i * z j) := by
  obtain ⟨C, hC, hbound⟩ := canonicalDomain_differenceEnergyBackground_bound n ha M
  have hB : 0 < max 1 M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨a / (max 1 M) ^ 2, C, div_pos ha (sq_pos_of_pos hB), hC, ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx B hj he A
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hb := hbound U hU hNE g D p x hx hj he
  have hi : ‖(canonicalDomain_differenceEnergyBackground U hU g D p x).1.1‖ ≤ C :=
    (norm_fst_le _).trans ((norm_fst_le _).trans hb)
  have hG : ‖B x‖ ≤ max 1 M := by
    apply le_trans _ (le_max_right _ _)
    simpa only [norm_iteratedFDeriv_zero] using hj 0 (by omega)
  have hxt : x ∈ (extChartAt (𝓡 n) p).target := by
    rw [canonicalOpen_extChart_target (𝕜 := ℝ) hU p]
    exact hx
  constructor
  · intro i j
    have hi' := (pi_norm_le_iff_of_nonneg hC0).mp hi i
    have hij := (pi_norm_le_iff_of_nonneg hC0).mp hi' j
    change ‖A i j‖ ≤ C at hij
    simpa only [Real.norm_eq_abs] using hij
  · intro z
    exact ContinuousLinearMap.inverse_sum_coordinates_coercive (B x)
      (g.isInvertible_chartCoefficients p hxt) ha.le hB hG he (WithLp.toLp 2 z)

end PoincareConjecture.M34
