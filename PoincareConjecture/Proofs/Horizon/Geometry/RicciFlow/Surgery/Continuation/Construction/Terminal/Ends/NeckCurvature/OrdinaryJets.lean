import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.ModelConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Second

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem abs_normalized_pullback_first_derivative_center_le_three
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (i j k : Fin 3) :
    |fderiv ℝ (fun p => roundCylinderTensorCoefficient N.normalized_pullback
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p j k) (0, s)
      (roundCylinderCoordinateBasis i)| ≤ 3 * N.epsilon := by
  have h := N.abs_normalized_pullback_first_component_le_three q hs ![i, j, k]
  rw [N.normalized_pullback_first_jet_center q hs] at h
  exact h

theorem abs_normalized_pullback_second_derivative_center_le_six
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a : Fin 4 → Fin 3) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    let E := fun (b : Fin 2 → Fin 3) p =>
      roundCylinderIteratedDerivative 0 c N.normalized_pullback 0 p b
    |fderiv ℝ (fun p => fderiv ℝ (E (fun j => a j.succ.succ)) p
      (roundCylinderCoordinateBasis (a 1))) (0, s)
      (roundCylinderCoordinateBasis (a 0))| ≤ 6 * N.epsilon := by
  classical
  dsimp only
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let E := fun (b : Fin 2 → Fin 3) p =>
    roundCylinderIteratedDerivative 0 c N.normalized_pullback 0 p b
  let J := fderiv ℝ (fun p => fderiv ℝ (E (fun j => a j.succ.succ)) p
    (roundCylinderCoordinateBasis (a 1))) (0, s)
    (roundCylinderCoordinateBasis (a 0))
  let R := fun (i : Fin 2) (d : Fin 3) =>
    fderiv ℝ (fun p => roundCylinderChristoffel 0 c p d (a 1)
      (a i.succ.succ)) (0, s) (roundCylinderCoordinateBasis (a 0)) *
        E (Function.update (fun j => a j.succ.succ) i d) (0, s)
  have hzero (b : Fin 2 → Fin 3) : |E b (0, s)| ≤ 2 * N.epsilon :=
    N.abs_normalized_pullback_metric_component_le_two q hs b
  have htwo :
      |roundCylinderIteratedDerivative 0 c N.normalized_pullback 2 (0, s) a| ≤
        4 * N.epsilon := N.abs_normalized_pullback_second_component_le_four q hs a
  have hR (i : Fin 2) : (∑ d : Fin 3, |R i d|) ≤ N.epsilon := by
    calc
      _ ≤ ∑ d : Fin 3, |fderiv ℝ (fun p => roundCylinderChristoffel 0 c p d
          (a 1) (a i.succ.succ)) (0, s) (roundCylinderCoordinateBasis (a 0))| *
            (2 * N.epsilon) := by
        apply Finset.sum_le_sum
        intro d _
        dsimp only [R]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hzero (Function.update (fun j => a j.succ.succ) i d)) (abs_nonneg _)
      _ ≤ (1 / 2) * (2 * N.epsilon) := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (sum_abs_fderiv_roundCylinderChristoffel_center_le_half q s
            (a 1) (a i.succ.succ) (a 0)) (by positivity [N.epsilon_pos])
      _ = _ := by ring
  have hsum : |∑ i : Fin 2, ∑ d : Fin 3, R i d| ≤ 2 * N.epsilon := by
    calc
      _ ≤ ∑ i : Fin 2, |∑ d : Fin 3, R i d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, ∑ d : Fin 3, |R i d| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 2, N.epsilon := Finset.sum_le_sum fun i _ => hR i
      _ = _ := by norm_num [Finset.sum_const, nsmul_eq_mul]
  have heq := N.normalized_pullback_second_jet_center q hs a
  change roundCylinderIteratedDerivative 0 c N.normalized_pullback 2 (0, s) a =
    J - ∑ i : Fin 2, ∑ d : Fin 3, R i d at heq
  have hJ : J = roundCylinderIteratedDerivative 0 c N.normalized_pullback 2
      (0, s) a + ∑ i : Fin 2, ∑ d : Fin 3, R i d := by linarith
  change |J| ≤ _
  rw [hJ]
  exact (abs_add_le _ _).trans ((add_le_add htwo hsum).trans_eq (by ring))

theorem abs_normalized_pullback_second_derivative_center_le_ten
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a : Fin 4 → Fin 3) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    let E := fun (b : Fin 2 → Fin 3) p =>
      roundCylinderIteratedDerivative 0 c N.normalized_pullback 0 p b
    |fderiv ℝ (fun p => fderiv ℝ (E (fun j => a j.succ.succ)) p
      (roundCylinderCoordinateBasis (a 1))) (0, s)
      (roundCylinderCoordinateBasis (a 0))| ≤ 10 * N.epsilon :=
  (N.abs_normalized_pullback_second_derivative_center_le_six q hs a).trans
    (by linarith [N.epsilon_pos])

end PoincareConjecture.EpsilonNeck
