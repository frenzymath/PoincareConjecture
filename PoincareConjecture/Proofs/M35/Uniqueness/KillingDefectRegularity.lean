import PoincareConjecture.Proofs.M35.Uniqueness.KillingDefectTensor
import PoincareConjecture.Proofs.M35.Uniqueness.KillingCovectorHeat
import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem killingDefectTensor_normSq_joint
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ico 0 G.lifetime ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × StandardCapSpace =>
        ((G.flow.metric p.1).tensorNorm
          (killingDefectTensor (G.flow.connection p.1) (X p.1)) p.2) ^ 2)
      (Ico 0 G.lifetime ×ˢ univ) := by
  let A := fun s => killingCovector (G.flow.metric s) (X s)
  have hA (s) : IsSmoothCovariantTensor (A s) :=
    isSmoothCovariantTensor_killingCovector _ _ (hX s)
  apply M04.contMDiffOn_flow_tensorNorm_sq G.flow
    (fun s => killingDefectTensor (G.flow.connection s) (X s))
    (fun s => isSmoothCovariantTensor_killingDefectTensor _ _ (hX s))
  intro U hU Y hY
  have hK := M04.contMDiffOn_flow_covariantTensorDerivative G.flow hA
    (killingCovector_joint G X hJoint) hU hY
  have hKs := M04.contMDiffOn_flow_covariantTensorDerivative G.flow hA
    (killingCovector_joint G X hJoint) hU
    (X := fun i => Y (Equiv.swap (0 : Fin 2) 1 i))
    (fun i => hY _)
  apply (hK.add hKs).congr
  intro p _
  simp only [Pi.add_apply]
  have hv : (fun i => Y i p.2) = ![Y 0 p.2, Y 1 p.2] := by
    ext i
    fin_cases i <;> rfl
  have hs : (fun i => Y (Equiv.swap (0 : Fin 2) 1 i) p.2) =
      ![Y 1 p.2, Y 0 p.2] := by
    ext i
    fin_cases i <;> simp
  rw [hv, hs]
  exact killing_defect_eq_covector_symmetrization (G.flow.connection p.1)
    (X p.1) (hX p.1) p.2 (Y 0 p.2) (Y 1 p.2)

theorem killingDefectTensor_normSq_le {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hX : ContDiff ℝ ∞ X) (x : EuclideanSpace ℝ (Fin n)) :
    (g.tensorNorm (killingDefectTensor D X) x) ^ 2 ≤
      4 * (g.tensorNorm (D.covariantTensorDerivative (killingCovector g X)) x) ^ 2 := by
  classical
  let e := g.orthonormalBasis x
  let K := D.covariantTensorDerivative (killingCovector g X)
  let v := fun a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
    fun i => e (a i)
  let s : (Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) ≃
      (Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :=
    { toFun := fun a => ![a 1, a 0]
      invFun := fun a => ![a 1, a 0]
      left_inv := by intro a; ext i; fin_cases i <;> rfl
      right_inv := by intro a; ext i; fin_cases i <;> rfl }
  have hswap : (∑ a, (K x (v (s a))) ^ 2) = ∑ a, (K x (v a)) ^ 2 :=
    s.sum_comp (fun a => (K x (v a)) ^ 2)
  have hdef (a) : killingDefectTensor D X x (v a) = K x (v a) + K x (v (s a)) := by
    have hv : v a = ![e (a 0), e (a 1)] := by ext i; fin_cases i <;> rfl
    have hs : v (s a) = ![e (a 1), e (a 0)] := by ext i; fin_cases i <;> rfl
    rw [hv, hs]
    exact killing_defect_eq_covector_symmetrization D X hX x _ _
  have hN (T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2) :
      (g.tensorNorm T x) ^ 2 = ∑ a, (T x (v a)) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [hN, hN]
  calc
    _ ≤ ∑ a, (2 * (K x (v a)) ^ 2 + 2 * (K x (v (s a))) ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      rw [hdef]
      nlinarith only [sq_nonneg (K x (v a) - K x (v (s a)))]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hswap]; ring

end PoincareConjecture.M35.Uniqueness
