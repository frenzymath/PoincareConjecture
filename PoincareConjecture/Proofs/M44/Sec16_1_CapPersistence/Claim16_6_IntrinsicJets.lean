import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_MetricBound










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]



theorem metric_covariant_error_sq_le_jet_error
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (B : CovariantTensorEvaluation 3 X 2) {j k : ℕ} (hjk : j ≤ k) (x : X) :
    (g.tensorNorm (D.iteratedCovariantTensorDerivative
      (fun y v => B y v - g.inner y (v 0) (v 1)) j) x) ^ 2 ≤
      singularMetricJetErrorSquared g D B k x := by
  exact Finset.single_le_sum (fun l _ => sq_nonneg
    (g.tensorNorm (D.iteratedCovariantTensorDerivative
      (fun y v => B y v - g.inner y (v 0) (v 1)) l) x))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hjk))



theorem metric_covariant_error_lt_of_jet_error
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (B : CovariantTensorEvaluation 3 X 2) {j k : ℕ} (hjk : j ≤ k)
    {x : X} {eta : ℝ} (heta : 0 < eta)
    (hjet : singularMetricJetErrorSquared g D B k x < eta ^ 2) :
    g.tensorNorm (D.iteratedCovariantTensorDerivative
      (fun y v => B y v - g.inner y (v 0) (v 1)) j) x < eta := by
  exact (sq_lt_sq₀ (Real.sqrt_nonneg _) heta.le).mp
    ((metric_covariant_error_sq_le_jet_error g D B hjk x).trans_lt hjet)



theorem metric_bilinear_error_le_of_jet_error
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (B : (x : X) → TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ)
    {k : ℕ} {x : X} {eta : ℝ} (heta : 0 < eta)
    (hjet : singularMetricJetErrorSquared g D (fun y v => B y (v 0) (v 1)) k x <
      eta ^ 2) (v w : TangentSpace (𝓡 3) x) :
    |B x v w - g.inner x v w| ≤ eta * (g.tangentNorm x v * g.tangentNorm x w) := by
  let H := B x - g.inner x
  let T : CovariantTensorEvaluation 3 X 2 :=
    fun y z => B y (z 0) (z 1) - g.inner y (z 0) (z 1)
  let A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 3) x) ℝ := {
    toFun := fun z => H (z 0) (z 1)
    map_update_add' := by
      intro _ z i a b
      fin_cases i <;> simp [map_add]
    map_update_smul' := by
      intro _ z i c a
      fin_cases i <;> simp [map_smul]
  }
  have hnorm : g.tensorNorm T x < eta :=
    metric_covariant_error_lt_of_jet_error g D
      (fun y z => B y (z 0) (z 1)) (Nat.zero_le k) heta hjet
  have h := abs_tensor_evaluation_le_tensorNorm g T x A (fun _ => rfl) ![v, w]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right hnorm.le
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))



theorem SurgeryCapClose.covariant_error_lt
    {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}
    (Q : SurgeryCapClose g₀ S g tip scale eta)
    {x : StandardCapSpace} (hx : x ∈ g₀.metric.ball 0 eta⁻¹)
    {j : ℕ} (hj : j ≤ ⌊eta⁻¹⌋₊) :
    g₀.metric.tensorNorm (g₀.connection.iteratedCovariantTensorDerivative
      (fun y v => scale⁻¹ ^ 2 * surgeryCapPullback g Q.map y v -
        g₀.metric.inner y (v 0) (v 1)) j) x < eta := by
  obtain ⟨bound, hbound, hjets⟩ := Q.jets
  exact metric_covariant_error_lt_of_jet_error g₀.metric g₀.connection
    (fun y v => scale⁻¹ ^ 2 * surgeryCapPullback g Q.map y v) hj Q.eta_pos
    ((hjets x hx).trans_lt hbound)

end PoincareConjecture
