import PoincareConjecture.Proofs.M47.PositiveGradientAlgebra
import PoincareConjecture.Proofs.M47.PositiveWeightedMaximum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.GradientEnergyTime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.SpatialCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Norm
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Regularity

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M47Positive

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem contMDiff_gradient_energy (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.gradient f x) (D.gradient f x)) := by
  have hgrad := D.contMDiff_gradient hf
  intro x
  have h := ((g.contMDiff x).clm_bundle_apply (hgrad x)).clm_bundle_apply (hgrad x)
  exact (Bundle.contMDiffAt_totalSpace.mp h).2

theorem continuousOn_scalar_gradient_energy
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J) :
    ContinuousOn (fun p : ℝ × M => (F.metric p.1).inner p.2
      ((F.connection p.1).gradient (F.connection p.1).scalarCurvature p.2)
      ((F.connection p.1).gradient (F.connection p.1).scalarCurvature p.2))
      (J ×ˢ univ) := by
  let T : (p : ℝ × M) →
      MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 n) p.2) ℝ := fun p =>
    { toFun := fun v => mvfderiv (𝓡 n) (F.connection p.1).scalarCurvature p.2 (v 0) *
        mvfderiv (𝓡 n) (F.connection p.1).scalarCurvature p.2 (v 1)
      map_update_add' := by
        intro _ v i a b
        fin_cases i <;> simp [map_add, add_mul, mul_add]
      map_update_smul' := by
        intro _ v i c a
        fin_cases i <;> simp [map_smul, mul_assoc, mul_left_comm] }
  have htrace := RicciFlowAnalysis.continuousOn_flow_tensorTrace F isOpen_univ T (by
    intro V hV _ X Y hX hY
    have hscalar := (hC.scalar_regular n M J F).mono
      (show J ×ˢ V ⊆ J ×ˢ univ from fun _ hp => ⟨hp.1, mem_univ _⟩)
    have hdx := RicciFlowAnalysis.contMDiffOn_mvfderiv_spatial hV hscalar hX
    have hdy := RicciFlowAnalysis.contMDiffOn_mvfderiv_spatial hV hscalar hY
    apply (hdx.mul hdy).continuousOn.congr
    intro p _
    rfl)
  have hid (p : ℝ × M) : (∑ i, T p
      ![(F.metric p.1).orthonormalBasis p.2 i, (F.metric p.1).orthonormalBasis p.2 i]) =
      (F.metric p.1).inner p.2
        ((F.connection p.1).gradient (F.connection p.1).scalarCurvature p.2)
        ((F.connection p.1).gradient (F.connection p.1).scalarCurvature p.2) := by
    simpa only [T, MultilinearMap.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      pow_two] using
      ((F.connection p.1).gradient_normSq_eq_sum_mvfderiv_sq
        (F.connection p.1).scalarCurvature p.2).symm
  simpa only [hid] using htrace

theorem gradient_energy_pairing (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    g.inner x (D.gradient (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x)
      (D.gradient f x) = 2 * D.hessian f x (D.gradient f x) (D.gradient f x) := by
  rw [D.inner_gradient, D.mvfderiv_normSq
    ((D.contMDiff_gradient hf x).mdifferentiableAt (by simp)),
    D.hessian_eq_inner_connection_gradient (hf x)]

theorem hasDerivAt_scalar_gradient_energy
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) :
    HasDerivAt (fun s => (F.metric s).inner x
      ((F.connection s).gradient (F.connection s).scalarCurvature x)
      ((F.connection s).gradient (F.connection s).scalarCurvature x))
      ((F.connection t).laplacian (fun y => (F.metric t).inner y
          ((F.connection t).gradient (F.connection t).scalarCurvature y)
          ((F.connection t).gradient (F.connection t).scalarCurvature y)) x -
        2 * (∑ i, ∑ j, ((F.connection t).hessian (F.connection t).scalarCurvature x
          ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x j)) ^ 2) +
        4 * (F.metric t).inner x
          ((F.connection t).gradient (F.connection t).scalarCurvature x)
          ((F.connection t).gradient (F.connection t).ricciNormSq x)) t := by
  let D := F.connection t
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hRs := hD.contMDiff_scalarCurvature
  have hSs := RicciFlow.contMDiff_ricciNormSq D hD
  have hspace (s : ℝ) :=
    (hC.tensor_calculus n M (F.metric s) (F.connection s)).contMDiff_scalarCurvature
  have hreg (y : M) : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (t, y) :=
    (hC.scalar_regular n M J F).contMDiffAt
      (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) Filter.univ_mem)
  have hdf (y : M) := (hC.scalar_evolution n M J F t (interior_subset ht) y).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have htime := F.hasDerivAt_gradient_normSq_of_time_derivative ht hspace hreg hdf x
  apply htime.congr_deriv
  have hB := D.bochner_identity hRs x
  have hLs := D.contMDiff_laplacian hRs
  have h2S : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (2 : ℝ) * D.ricciNormSq y) := by
    have hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (2 : ℝ)) := contMDiff_const
    exact hc.smul hSs
  rw [(F.metric t).symm x (D.gradient D.scalarCurvature x), D.inner_gradient,
    mvfderiv_fun_add ((hLs x).mdifferentiableAt (by simp))
      ((h2S x).mdifferentiableAt (by simp))]
  simp only [add_apply, mvfderiv_const_mul]
  rw [(F.metric t).symm x (D.gradient D.scalarCurvature x), D.inner_gradient]
  linarith only [hB]

end PoincareConjecture.M47Positive
