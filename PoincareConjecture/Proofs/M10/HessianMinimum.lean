import PoincareConjecture.Proofs.M10.PreferredHessian
import PoincareConjecture.Proofs.M10.LineSecondDerivative









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem isLocalMin_preferredCoordinates {f : M → ℝ} {q : M} (hmin : IsLocalMin f q) :
    IsLocalMin (f ∘ (extChartAt (𝓡 n) q).symm) (extChartAt (𝓡 n) q q) := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := 1) q).contMDiffAt
    (extChartAt_target_mem_nhds (I := 𝓡 n) q)
  apply IsLocalMin.comp_continuous _ hi.continuousAt
  simpa only [extChartAt_to_inv] using hmin


theorem mvfderiv_eq_zero_of_isLocalMin_hessian {f : M → ℝ} {q : M}
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f q) (hmin : IsLocalMin f q) :
    mvfderiv (𝓡 n) f q = 0 := by
  ext v
  rw [← preferredChart_scalar_derivative q hf v,
    (isLocalMin_preferredCoordinates hmin).fderiv_eq_zero]
  rfl


theorem hessian_self_nonneg_of_isLocalMin (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {f : M → ℝ} {q : M} (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q)
    (hmin : IsLocalMin f q) (v : TangentSpace (𝓡 n) q) :
    0 ≤ D.hessian f q v v := by
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) 2 (extChartAt (𝓡 n) q).symm
      (extChartAt (𝓡 n) q q) :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      (extChartAt_target_mem_nhds (I := 𝓡 n) q)
  have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f
      ((extChartAt (𝓡 n) q).symm (extChartAt (𝓡 n) q q)) := by
    simpa only [extChartAt_to_inv] using hf
  have hcoord := (hf'.comp (extChartAt (𝓡 n) q q) hi).contDiffAt
  have hzero := mvfderiv_eq_zero_of_isLocalMin_hessian (hf.mdifferentiableAt two_ne_zero) hmin
  unfold LeviCivitaData.hessian LeviCivitaData.hessianOnFields
  rw [FiberBundle.extend_apply_self, preferredField_second_scalar_derivative q hf v,
    hzero, zero_apply, sub_zero]
  exact second_fderiv_nonneg_of_isLocalMin hcoord (isLocalMin_preferredCoordinates hmin) v


theorem laplacian_nonneg_of_isLocalMin (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {f : M → ℝ} {q : M} (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q)
    (hmin : IsLocalMin f q) : 0 ≤ D.laplacian f q := by
  exact Finset.sum_nonneg (fun i _ ↦ hessian_self_nonneg_of_isLocalMin g D hf hmin
    (g.orthonormalBasis q i))

end PoincareConjecture.M10
