import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderCurvature










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance quadraticCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance quadraticCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace



theorem model_evolvingCylinder_zero_quadratic_bounds {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 0) (v : E) :
    ‖v‖ ^ 2 ≤ evolvingCylinderModelField t 0 v v ∧
      evolvingCylinderModelField t 0 v v ≤ 4 * ‖v‖ ^ 2 := by
  have hsplit := congrArg (fun A : MetricCoefficient 3 => A v v)
    cylinderHorizontalForm_add_vertical
  change cylinderHorizontalForm v v + cylinderHeightCovector v * cylinderHeightCovector v =
    inner ℝ v v at hsplit
  rw [real_inner_self_eq_norm_sq] at hsplit
  have hH : 0 ≤ cylinderHorizontalForm v v := by
    rw [cylinderHorizontalForm_apply]
    exact real_inner_self_nonneg
  have hV : 0 ≤ cylinderHeightCovector v * cylinderHeightCovector v := mul_self_nonneg _
  rw [evolvingCylinderModelField_zero]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  constructor <;> nlinarith [ht.1, ht.2]



theorem model_metricCoefficient_quadratic_error (A C : MetricCoefficient 3)
    {delta : ℝ} (hnear : ‖A - C‖ ≤ delta) (v : E) :
    |A v v - C v v| ≤ delta * ‖v‖ ^ 2 := by
  change |(A - C) v v| ≤ _
  calc
    _ ≤ ‖A - C‖ * ‖v‖ * ‖v‖ := (A - C).le_opNorm₂ v v
    _ ≤ delta * ‖v‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnear (norm_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring




theorem model_evolvingCylinder_perturbed_quadratic_bounds {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 0) (A : MetricCoefficient 3)
    (hnear : ‖A - evolvingCylinderModelField t 0‖ ≤ (1 / 2 : ℝ)) (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ A v v ∧ A v v ≤ (9 / 2 : ℝ) * ‖v‖ ^ 2 := by
  obtain ⟨hlo, hhi⟩ := model_evolvingCylinder_zero_quadratic_bounds ht v
  obtain ⟨heLo, heHi⟩ := abs_le.mp (model_metricCoefficient_quadratic_error A _ hnear v)
  constructor <;> linarith

end PoincareConjecture.M45
