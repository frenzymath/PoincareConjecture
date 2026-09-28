import PoincareConjecture.Definitions.Ch13.MetricSurgery
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.NormBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]

theorem metric_error_sq_le_jet_error
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (B : CovariantTensorEvaluation 3 X 2) (k : ℕ) (x : X) :
    (g.tensorNorm (fun y v => B y v - g.inner y (v 0) (v 1)) x) ^ 2 ≤
      singularMetricJetErrorSquared g D B k x := by
  let f : ℕ → ℝ := fun j => (g.tensorNorm (D.iteratedCovariantTensorDerivative
    (fun y v => B y v - g.inner y (v 0) (v 1)) j) x) ^ 2
  have h : f 0 ≤ ∑ j ∈ Finset.range (k + 1), f j :=
    Finset.single_le_sum (f := f) (fun j _ => show 0 ≤ f j from sq_nonneg _)
      (Finset.mem_range.mpr (Nat.zero_lt_succ k))
  exact h

theorem metric_quadratic_bounds_of_jet_error
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (B : (x : X) → TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ)
    {k : ℕ} {x : X} {eta : ℝ} (heta : 0 < eta)
    (hjet : singularMetricJetErrorSquared g D (fun y v => B y (v 0) (v 1)) k x <
      eta ^ 2) (v : TangentSpace (𝓡 3) x) :
    (1 - eta) * g.inner x v v ≤ B x v v ∧
      B x v v ≤ (1 + eta) * g.inner x v v := by
  let H := B x - g.inner x
  let T : CovariantTensorEvaluation 3 X 2 :=
    fun y w => B y (w 0) (w 1) - g.inner y (w 0) (w 1)
  let A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 3) x) ℝ := {
    toFun := fun w => H (w 0) (w 1)
    map_update_add' := by
      intro _ w i a b
      fin_cases i <;> simp [map_add]
    map_update_smul' := by
      intro _ w i c a
      fin_cases i <;> simp [map_smul]
  }
  have hA (w : Fin 2 → TangentSpace (𝓡 3) x) : T x w = A w := rfl
  have hnorm : g.tensorNorm T x < eta := by
    have hs := (metric_error_sq_le_jet_error g D (fun y w => B y (w 0) (w 1)) k x).trans_lt
      hjet
    exact (sq_lt_sq₀ (Real.sqrt_nonneg _) heta.le).mp hs
  have heval := abs_tensor_evaluation_le_tensorNorm g T x A hA ![v, v]
  have hv : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hprod : (∏ r : Fin 2, g.tangentNorm x (![v, v] r)) = g.inner x v v := by
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      RiemannianMetric.tangentNorm, ← sq, Real.sq_sqrt hv]
  rw [hprod] at heval
  have habs : |B x v v - g.inner x v v| ≤ eta * g.inner x v v :=
    heval.trans (mul_le_mul_of_nonneg_right hnorm.le hv)
  have h := abs_le.mp habs
  constructor <;> nlinarith [h.1, h.2]

theorem SurgeryCapClose.quadratic_bounds
    {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}
    (Q : SurgeryCapClose g₀ S g tip scale eta)
    {x : StandardCapSpace} (hx : x ∈ g₀.metric.ball 0 eta⁻¹)
    (v : TangentSpace (𝓡 3) x) :
    (1 - eta) * g₀.metric.inner x v v ≤
        scale⁻¹ ^ 2 * g.inner (Q.map x)
          (mfderiv (𝓡 3) (𝓡 3) Q.map x v) (mfderiv (𝓡 3) (𝓡 3) Q.map x v) ∧
      scale⁻¹ ^ 2 * g.inner (Q.map x)
          (mfderiv (𝓡 3) (𝓡 3) Q.map x v) (mfderiv (𝓡 3) (𝓡 3) Q.map x v) ≤
        (1 + eta) * g₀.metric.inner x v v := by
  obtain ⟨bound, hbound, hjets⟩ := Q.jets
  let B : StandardCapSpace → StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
    fun y =>
      let L : StandardCapSpace →L[ℝ] StandardCapSpace := mfderiv (𝓡 3) (𝓡 3) Q.map y
      let H : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g.inner (Q.map y)
      scale⁻¹ ^ 2 • H.bilinearComp L L
  exact metric_quadratic_bounds_of_jet_error g₀.metric g₀.connection B Q.eta_pos
    ((hjets x hx).trans_lt hbound) v

end PoincareConjecture
