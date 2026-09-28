import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedTimeContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Barriers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {J : Set ℝ} {F : RicciFlow n M J} {O : M}

theorem deriv_perturbedHamiltonFixedQuadratic_pos
    (hC : RicciFlowCurvatureTheory.{u}) (S : RicciFlow.SmoothExhaustion F O)
    {t K T ε δ A : ℝ} (ht : t ∈ interior J) (htpos : 0 < t)
    (hT : t ≤ T) (hK : 0 ≤ K) (x : M)
    (hbound : ∀ j ≤ 2, (F.connection t).curvatureDerivativeNorm j x ≤ K)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hA : hamiltonPerturbationErrorBound n K T + (n : ℝ) * S.bound < A)
    (hsmall : hamiltonPerturbationErrorBound n K T * δ ≤ ε)
    (hψone : δ * Real.exp (A * t) ≤ 1)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a)
    (hnonzero : Real.sqrt (∑ a, ∑ c, (U a c) ^ 2) ≠ 0 ∨
      Real.sqrt (∑ a, (W a) ^ 2) ≠ 0)
    (hQ : ∀ᶠ y in 𝓝 x, let b := (F.metric t).orthonormalBasis y
      (Matrix.fromBlocks
        (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) =>
          (F.connection t).curvatureTensor y (b ac.1) (b ac.2) (b de.1) (b de.2) +
            (δ * Real.exp (A * t)) * twoFormIdentity ac.1 ac.2 de.1 de.2)
        (fun ac d => hamiltonP (F.connection t) y (b ac.1) (b ac.2) (b d))
        (fun c de => hamiltonP (F.connection t) y (b de.1) (b de.2) (b c))
        (fun a c => hamiltonM (F.connection t) t y (b a) (b c) +
          (ε * Real.exp (A * t) * S.toFun y / t) * (if a = c then 1 else 0))).PosSemidef)
    (hnull : perturbedHamiltonFixedQuadratic F 0 t x
      (fun s y => ε * Real.exp (A * s) * S.toFun y / s)
      (fun s => δ * Real.exp (A * s)) U W t = 0) :
    0 < deriv (perturbedHamiltonFixedQuadratic F 0 t x
      (fun s y => ε * Real.exp (A * s) * S.toFun y / s)
      (fun s => δ * Real.exp (A * s)) U W) t := by
  have hαtime := ((S.hasDerivAt_exp_mul ε A t x).div
    (hasDerivAt_id t) htpos.ne').differentiableAt
  have hψtime := (((hasDerivAt_id t).const_mul A).exp.const_mul δ).differentiableAt
  have hαspace : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => ε * Real.exp (A * t) * S.toFun y / t) := by
    simpa only [mul_div_right_comm, Pi.mul_apply] using!
      (contMDiff_const.mul S.smooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => (ε * Real.exp (A * t) / t) * S.toFun y))
  have hα : 0 ≤ ε * Real.exp (A * t) * S.toFun x / t :=
    div_nonneg (mul_nonneg (mul_nonneg hε.le (Real.exp_nonneg _))
      (zero_le_one.trans (S.one_le x))) htpos.le
  have hd := deriv_perturbedHamiltonFixedQuadratic_ge_of_bound hC F 0
    ht (by simpa using htpos) (by simpa using hT) hK x hbound
    (fun s y => ε * Real.exp (A * s) * S.toFun y / s)
    (fun s => δ * Real.exp (A * s)) hαtime hψtime hαspace
    hα (mul_nonneg hδ.le (Real.exp_nonneg _)) hψone U W hU
    (by simpa only [sub_zero] using hQ) hnull
  have hs := S.exp_mul_div_quadratic_heat_gt hε hδ hA
    (interior_subset ht) htpos hsmall hnonzero x
  simp only [Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg (W a))),
    Real.sq_sqrt (Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun c _ => sq_nonneg (U a c))))] at hs
  exact hs.trans_le (by simpa only [sub_zero] using hd)

end Poincare.RicciFlow.Harnack
