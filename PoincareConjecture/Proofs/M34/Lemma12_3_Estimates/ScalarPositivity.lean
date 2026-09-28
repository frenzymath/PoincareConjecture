import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.TipPositivity
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.GlobalBounds
import PoincareConjecture.Proofs.M04.PointwiseFlatness

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

theorem initialAngularNumerator_pos (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 ≤ r) :
    0 < g₀.connection.curvatureTensor (EuclideanSpace.single (0 : Fin 3) r)
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
  obtain ⟨δ, hδ, htip⟩ := initialTip_angular_positive_segment g₀
  by_cases hsmall : r < δ
  · exact htip r hr hsmall
  have hrpos : 0 < r := hδ.trans_le (le_of_not_gt hsmall)
  have hh : 0 < δ / 2 := half_pos hδ
  have hhalf := htip (δ / 2) hh.le (half_lt_self hδ)
  rw [initialCurvatureTensor_angular_axis g₀ hh] at hhalf
  have hqhalf : initialWeightedSlope g₀ (δ / 2) ^ 2 < 1 := by
    have hm := (div_pos_iff_of_pos_right (sq_pos_of_pos hh)).mp hhalf
    have hp := (mul_pos_iff_of_pos_left (initialCoefficients_pos g₀ (δ / 2)).2).mp hm
    linarith
  have hqhalf' : initialWeightedSlope g₀ (δ / 2) < 1 := by nlinarith
  have hle := initialWeightedSlope_antitoneOn g₀ hh hrpos
    ((half_le_self hδ.le).trans (le_of_not_gt hsmall))
  have hq : initialWeightedSlope g₀ r < 1 := hle.trans_lt hqhalf'
  have hn := initialWeightedSlope_nonneg g₀ hrpos
  have hp : 0 < 1 - initialWeightedSlope g₀ r ^ 2 := by
    have hm : 0 < (1 - initialWeightedSlope g₀ r) * (1 + initialWeightedSlope g₀ r) :=
      mul_pos (sub_pos.mpr hq) (by linarith)
    nlinarith
  rw [initialCurvatureTensor_angular_axis g₀ hrpos]
  exact div_pos (mul_pos (initialCoefficients_pos g₀ r).2 hp) (sq_pos_of_pos hrpos)

theorem initialScalarCurvature_axis_pos (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 ≤ r) :
    0 < g₀.connection.scalarCurvature (EuclideanSpace.single (0 : Fin 3) r) := by
  let x : StandardCapSpace := EuclideanSpace.single 0 r
  have hn := M04.nonneg_scalar_of_nonnegativeSectionalAt g₀.connection x
    (g₀.nonnegative_sectional x)
  have hp := initialAngularNumerator_pos g₀ hr
  by_contra h
  have hs : g₀.connection.scalarCurvature x = 0 := le_antisymm (le_of_not_gt h) hn
  have hz := M04.curvatureTensor_eq_zero_of_nonnegativeSectionalAt_scalar_zero
    g₀.connection x (g₀.nonnegative_sectional x) hs
    (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
    (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
    (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  change g₀.connection.curvatureTensor (EuclideanSpace.single (0 : Fin 3) r) _ _ _ _ = 0 at hz
  rw [hz] at hp
  exact (lt_irrefl 0) hp

theorem initialScalarCurvature_rotation (g₀ : StandardInitialMetric)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x : StandardCapSpace) :
    g₀.connection.scalarCurvature (standardRotation A x) = g₀.connection.scalarCurvature x := by
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ (standardRotation A) :=
    contMDiff_iff_contDiff.mpr (capRotationIsometry A).toContinuousLinearMap.contDiff
  exact (g₀.connection.scalarCurvature_eq_of_local_isometry g₀.connection isOpen_univ
    hf.contMDiffOn (fun y _ u v => (g₀.rotation_invariant A y u v).symm) (mem_univ x)).symm

theorem initialScalarCurvature_pos (g₀ : StandardInitialMetric) (x : StandardCapSpace) :
    0 < g₀.connection.scalarCurvature x := by
  obtain ⟨A, hA⟩ := exists_standardRotation_axis x
  rw [← hA, initialScalarCurvature_rotation]
  exact initialScalarCurvature_axis_pos g₀ (norm_nonneg x)

theorem standardCapEstimate_exists (g₀ : StandardInitialMetric) :
    Nonempty (StandardCapEstimate g₀) :=
  standardCapEstimate_of_scalar_pos g₀ (initialScalarCurvature_pos g₀)

end PoincareConjecture.M34
