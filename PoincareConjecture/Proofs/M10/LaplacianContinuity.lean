import PoincareConjecture.Proofs.M10.ChartDivergence
import PoincareConjecture.Proofs.M10.WeightedMetricDual
import PoincareConjecture.Proofs.M10.LaplacianLinearity
import PoincareConjecture.Proofs.M10.RegularGerms









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem tsupport_laplacian_subset (D : LeviCivitaData g) (f : M → ℝ) :
    tsupport (D.laplacian f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hnot
  apply hx
  exact (laplacian_eq_of_eventuallyEq D (notMem_tsupport_iff_eventuallyEq.mp hnot)).trans
    (laplacian_const_scalar D 0 x)

set_option backward.isDefEq.respectTransparency false in

theorem continuous_laplacian (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) 2 f) : Continuous (D.laplacian f) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let e := extChartAt (𝓡 n) q
  let B := pullbackMetricForm g e.symm
  let ρ := pullbackJacobian g e.symm
  let u := f ∘ e.symm
  let V := weightedMetricDual B ρ u
  let δ := fun y ↦ LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (fderiv ℝ V y).toLinearMap
  have hU : IsOpen e.target := isOpen_extChartAt_target q
  have hB : ContDiffOn ℝ 1 B e.target := (chartMetricForm_contDiffOn g q).of_le (by simp)
  have hρ : ContDiffOn ℝ 1 ρ e.target := (chartJacobian_contDiffOn g q).of_le (by simp)
  have hu : ContDiffOn ℝ 2 u e.target := fun y hy ↦
    (fixedChart_scalar_contDiffAt q hy (hf (e.symm y))).contDiffWithinAt
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ e.target) : (B y).IsInvertible :=
    positive_bilinear_isInvertible _ (fun _ hv ↦ chartMetricForm_pos g q hy hv)
  have hρpos (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ e.target) : 0 < ρ y := by
    obtain ⟨A, hA⟩ := inverseChart_mfderiv_isInvertible q hy
    apply pullbackJacobian_pos g
    rw [← hA]
    exact A.injective
  have hV : ContDiffOn ℝ 1 V e.target := fun y hy ↦
    (weightedMetricDual_contDiffAt (hB.contDiffAt (hU.mem_nhds hy))
      (hρ.contDiffAt (hU.mem_nhds hy)) (hu.contDiffAt (hU.mem_nhds hy))
      (hi y hy)).contDiffWithinAt
  have hδ : ContinuousOn δ e.target := by
    dsimp only [δ]
    simp_rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
    exact continuousOn_finsetSum _ (fun i _ ↦
      continuousOn_const.inner
        ((hV.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const))
  have hquot : ContinuousAt (fun y ↦ δ y / ρ y) (e q) :=
    (hδ.continuousAt (extChartAt_target_mem_nhds (I := 𝓡 n) q)).div
      (hρ.continuousOn.continuousAt (extChartAt_target_mem_nhds (I := 𝓡 n) q))
      (hρpos (e q) (mem_extChartAt_target q)).ne'
  apply (hquot.comp (continuousAt_extChartAt (I := 𝓡 n) q)).congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓡 n) q] with x hx
  apply (eq_div_iff (hρpos (e x) (e.map_source hx)).ne').mpr
  have h := chart_laplacian_divergence g D q (e.map_source hx) (hf (e.symm (e x)))
  change ρ (e x) * D.laplacian f (e.symm (e x)) = δ (e x) at h
  simpa only [e.left_inv hx, mul_comm] using h

end PoincareConjecture.M10
