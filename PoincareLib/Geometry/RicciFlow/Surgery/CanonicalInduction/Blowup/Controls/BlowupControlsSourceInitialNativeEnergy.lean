import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CapPersistenceIntrinsicError
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.CylinderTimeWeights
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Cylinder.CylinderTimeComparison

/-!
# Uniform native energy at nonpositive model times

The exact model correction preserves every covariant error array.
Earlier cylinder times decrease its inverse-Gram contraction, so one
time-zero ordinary-to-native constant controls all nonpositive times.
Morgan--Tian Lemma 17.7, pp. 405-406; native-past F1.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareMT.M47

open M34 M44

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The same complete error arrays have smaller squared norm at
nonpositive model time than their exact time-zero correction. -/
theorem source_initial_native_energy_le_static {u : ℝ} (hu : u ≤ 0)
    (B : RoundCylinderTwoTensor) (m : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u B m z ≤
      roundCylinderJetErrorSquared 0 (staticCylinderCorrection u B) m z := by
  unfold roundCylinderJetErrorSquared
  simp only [staticCylinderCorrection_iteratedDerivative (hu.trans_lt zero_lt_one)]
  exact Finset.sum_le_sum fun k _ =>
    M35.roundCylinderTensorNormSquared_mono_time hu zero_lt_one z.1 z.2 _

/-- One constant precedes the model time, physical tensor and every
native center. All finite coefficient error jets and slots are retained. -/
theorem exists_source_initial_native_coefficient_bound (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : ℝ}, u ≤ 0 →
      ∀ (B : RoundCylinderTwoTensor) (theta : UnitTwoSphere) (c : ℝ),
      (∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ theta) y a b) (0, c)) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ m, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ theta) y a b -
          roundCylinderGram u (chartAt E₂ theta) y a b) (0, c)‖ ≤ A) →
      roundCylinderJetErrorSquared u B m (theta, c) ≤ K * A ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := capPersistence_exists_intrinsic_error_bound m
  refine ⟨K, hK, ?_⟩
  intro u hu B theta c hB A hA hjets
  apply (source_initial_native_energy_le_static hu B m (theta, c)).trans
  apply hbound (staticCylinderCorrection u B) theta c
  · intro a b
    simp only [staticCylinderCorrection_coefficient]
    exact ((hB a b).add (capPersistence_modelGram_contDiff 0 theta a b).contDiffAt).sub
      (capPersistence_modelGram_contDiff u theta a b).contDiffAt
  · exact hA
  · intro j hj a b
    have heq : (fun y =>
        roundCylinderTensorCoefficient (staticCylinderCorrection u B) (chartAt E₂ theta)
          y a b - roundCylinderGram 0 (chartAt E₂ theta) y a b) =
        (fun y => roundCylinderTensorCoefficient B (chartAt E₂ theta) y a b -
          roundCylinderGram u (chartAt E₂ theta) y a b) := by
      funext y
      rw [staticCylinderCorrection_coefficient]
      ring
    rw [heq]
    exact hjets j hj a b

end PoincareMT.M47
