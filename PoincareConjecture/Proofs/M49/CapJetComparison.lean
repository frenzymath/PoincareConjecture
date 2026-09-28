import PoincareConjecture.Definitions.Ch13.MetricSurgery
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.NormBounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M49

theorem tensorNorm_sq_le_singularMetricJetErrorSquared
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (B : CovariantTensorEvaluation 3 X 2) (k : ℕ) (x : X) :
    (g.tensorNorm (fun y v => B y v - g.inner y (v 0) (v 1)) x) ^ 2 ≤
      singularMetricJetErrorSquared g D B k x := by
  unfold singularMetricJetErrorSquared
  have h := Finset.single_le_sum (s := Finset.range (k + 1)) (a := 0)
    (f := fun j => (g.tensorNorm (D.iteratedCovariantTensorDerivative
      (fun y v => B y v - g.inner y (v 0) (v 1)) j) x) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.zero_lt_succ k))
  exact h

theorem tensorNorm_lt_of_singularMetricJetErrorSquared_lt
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (B : CovariantTensorEvaluation 3 X 2) (k : ℕ) (x : X)
    {eta : ℝ} (heta : 0 < eta)
    (h : singularMetricJetErrorSquared g D B k x < eta ^ 2) :
    g.tensorNorm (fun y v => B y v - g.inner y (v 0) (v 1)) x < eta := by
  have hsq := (tensorNorm_sq_le_singularMetricJetErrorSquared g D B k x).trans_lt h
  nlinarith

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {h eta : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem surgeryCapClose_bilinear_error_le (C : SurgeryCapClose g₀ S g tip h eta)
    {p : StandardCapSpace} (hp : p ∈ g₀.metric.ball 0 eta⁻¹)
    (v w : TangentSpace (𝓡 3) p) :
    |h⁻¹ ^ 2 * g.inner (C.map p)
        (mfderiv (𝓡 3) (𝓡 3) C.map p v) (mfderiv (𝓡 3) (𝓡 3) C.map p w) -
      g₀.metric.inner p v w| ≤
      eta * g₀.metric.tangentNorm p v * g₀.metric.tangentNorm p w := by
  let B : CovariantTensorEvaluation 3 StandardCapSpace 2 :=
    fun x z => h⁻¹ ^ 2 * surgeryCapPullback g C.map x z
  let T : CovariantTensorEvaluation 3 StandardCapSpace 2 :=
    fun x z => B x z - g₀.metric.inner x (z 0) (z 1)
  let A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 3) p) ℝ :=
    { toFun := T p
      map_update_add' := by
        intro _ z i a b
        fin_cases i <;>
          simp [T, B, surgeryCapPullback, map_add, mul_add] <;> ring
      map_update_smul' := by
        intro _ z i r a
        fin_cases i <;>
          simp [T, B, surgeryCapPullback, map_smul, smul_eq_mul] <;> ring }
  obtain ⟨b, hb, hbound⟩ := C.jets
  have hnorm : g₀.metric.tensorNorm T p < eta :=
    tensorNorm_lt_of_singularMetricJetErrorSquared_lt g₀.metric g₀.connection B
      ⌊eta⁻¹⌋₊ p C.eta_pos ((hbound p hp).trans_lt hb)
  have heval := abs_tensor_evaluation_le_tensorNorm g₀.metric T p A
    (fun _ => rfl) ![v, w]
  have hv : 0 ≤ g₀.metric.tangentNorm p v := Real.sqrt_nonneg _
  have hw : 0 ≤ g₀.metric.tangentNorm p w := Real.sqrt_nonneg _
  calc
    _ ≤ g₀.metric.tensorNorm T p *
        (g₀.metric.tangentNorm p v * g₀.metric.tangentNorm p w) := by
      simpa only [T, B, surgeryCapPullback, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using heval
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hnorm.le (mul_nonneg hv hw)]

set_option backward.isDefEq.respectTransparency false in

theorem surgeryCapClose_quadratic_bounds (C : SurgeryCapClose g₀ S g tip h eta)
    {p : StandardCapSpace} (hp : p ∈ g₀.metric.ball 0 eta⁻¹)
    (v : TangentSpace (𝓡 3) p) :
    (1 - eta) * g₀.metric.inner p v v ≤
      h⁻¹ ^ 2 * g.inner (C.map p)
        (mfderiv (𝓡 3) (𝓡 3) C.map p v) (mfderiv (𝓡 3) (𝓡 3) C.map p v) ∧
      h⁻¹ ^ 2 * g.inner (C.map p)
        (mfderiv (𝓡 3) (𝓡 3) C.map p v) (mfderiv (𝓡 3) (𝓡 3) C.map p v) ≤
        (1 + eta) * g₀.metric.inner p v v := by
  have hnonneg : 0 ≤ g₀.metric.inner p v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g₀.metric.pos p v hv).le
  have he := surgeryCapClose_bilinear_error_le C hp v v
  have hnorm : g₀.metric.tangentNorm p v * g₀.metric.tangentNorm p v =
      g₀.metric.inner p v v := by
    exact (pow_two _).symm.trans (Real.sq_sqrt hnonneg)
  rw [mul_assoc, hnorm] at he
  have he' := abs_le.mp he
  constructor <;> nlinarith

set_option backward.isDefEq.respectTransparency false in

theorem surgeryCapClose_mfderiv_injective (C : SurgeryCapClose g₀ S g tip h eta)
    (heta : eta < 1) {p : StandardCapSpace} (hp : p ∈ g₀.metric.ball 0 eta⁻¹) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) C.map p) := by
  apply (mfderiv (𝓡 3) (𝓡 3) C.map p).toLinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  have hzero : mfderiv (𝓡 3) (𝓡 3) C.map p v = 0 := hv
  have he := (surgeryCapClose_quadratic_bounds C hp v).1
  rw [hzero, map_zero, mul_zero] at he
  have hnorm : g₀.metric.inner p v v ≤ 0 := by nlinarith
  have hv0 : v = 0 := by
    by_contra hne
    have hpos : 0 < g₀.metric.inner p v v := g₀.metric.pos p v hne
    exact (not_lt_of_ge hnorm) hpos
  simpa only [hv0] using (Submodule.zero_mem (⊥ : Submodule ℝ (TangentSpace (𝓡 3) p)))

end PoincareConjecture.M49
