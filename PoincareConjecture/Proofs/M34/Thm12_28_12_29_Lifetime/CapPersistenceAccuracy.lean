import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceTransferTolerance
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckScalar











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)




theorem capPersistence_exists_common_neck_accuracy (epsilon tau eta : ℝ)
    (hepsilon : 0 < epsilon) (htau : 0 < tau) (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ epsilon / 4 ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace E₃ M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (N : EpsilonNeck g), N.epsilon < delta0 →
        Nat.floor epsilon⁻¹ + 1 ≤ Nat.floor N.epsilon⁻¹ ∧
        (∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
          ∀ j ≤ Nat.floor epsilon⁻¹, ∀ a b : Fin 3,
            ‖iteratedFDeriv ℝ j (fun y =>
              roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
                roundCylinderPullback g N.coordinate_map z v w) (chartAt E₂ q) y a b -
                  roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ tau / 2) ∧
        (∀ x ∈ closure N.carrier,
          |N.scale ^ 2 * N.connection.scalarCurvature x - 1| ≤ min (eta / 2) (1 / 10)) := by
  obtain ⟨d1, hd1, _hd1epsilon, herror⟩ :=
    capPersistence_exists_old_transfer_accuracy epsilon tau hepsilon htau
  have hsmall : 0 < min (eta / 2) (1 / 10 : ℝ) :=
    lt_min (div_pos heta (by norm_num)) (by norm_num)
  obtain ⟨d2, hd2, hscalar⟩ := capPersistence_exists_neck_scalar_accuracy hsmall
  let delta0 := min d1 (min d2 (epsilon / 4))
  have hdelta0 : 0 < delta0 :=
    lt_min hd1 (lt_min hd2 (div_pos hepsilon (by norm_num)))
  refine ⟨delta0, hdelta0, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro M _ _ _ _ g N hN
  have hN1 : N.epsilon < d1 := hN.trans_le (min_le_left _ _)
  have hN2 : N.epsilon < d2 :=
    hN.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨hm, hjets⟩ := herror N.epsilon N.epsilon_pos hN1
  exact ⟨hm, hjets _ N.metric_comparison.close, (hscalar M g N hN2).2⟩

end PoincareConjecture.M34
