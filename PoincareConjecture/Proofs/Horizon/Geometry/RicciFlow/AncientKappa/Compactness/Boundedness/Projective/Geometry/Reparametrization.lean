import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Reparametrization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.CylinderCover

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem norm_fderiv_centeredParametrization_rechart_le
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε r : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hr : 0 < r)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0
      (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g f z v w))
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-ε⁻¹) ε⁻¹)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (e : RoundCylinderCoordinates ≃L[ℝ] E) :
    ‖fderiv ℝ (g.parametrizedCoefficients
      (centeredParametrization f q ∘ e.symm)) (e (0, s))‖ ≤
      216 * ε * r ^ 2 * ‖e.symm.toContinuousLinearMap‖ ^ 3 := by
  let T : E →L[ℝ] RoundCylinderCoordinates := e.symm.toContinuousLinearMap
  let p := e (0, s)
  let B := g.parametrizedCoefficients (centeredParametrization f q ∘ T)
  let A := fun y => (normalizedCenteredCoefficients g f (r⁻¹ ^ 2) q (T y)).bilinearComp T T
  have hp : T p = (0, s) := e.symm_apply_apply _
  have hB : DifferentiableAt ℝ B p := by
    apply (g.contDiffAt_parametrizedCoefficients ?_).differentiableAt (by simp)
    apply (centeredParametrization_contMDiffAt hf q (y := T p) ?_).comp p T.contMDiff.contMDiffAt
    simpa only [hp] using hs
  have heq : (fun y => r⁻¹ ^ 2 • B y) =ᶠ[𝓝 p] A := by
    have hnear : ∀ᶠ y in 𝓝 p, (T y).2 ∈ Ioo (-ε⁻¹) ε⁻¹ :=
      (continuous_snd.comp T.continuous).continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (by simpa only [Function.comp_apply, hp] using hs))
    filter_upwards [hnear] with y hy
    dsimp only [B, A]
    rw [g.parametrizedCoefficients_comp_linear T
      ((centeredParametrization_contMDiffAt hf q hy).mdifferentiableAt (by simp))]
    ext v w
    rfl
  have hA : ‖fderiv ℝ A p‖ ≤ 216 * ε * ‖T‖ ^ 3 := by
    have hdiff : DifferentiableAt ℝ (normalizedCenteredCoefficients g f (r⁻¹ ^ 2) q) (T p) := by
      rw [hp]
      exact (normalizedCenteredCoefficients_contDiffAt g hf (r⁻¹ ^ 2) q
        (y := (0, s)) hs).differentiableAt (by simp)
    have h := norm_fderiv_bilinearComp_linear_le T hdiff
    rw [hp] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (norm_fderiv_normalizedCenteredCoefficients_le g hε hεone hf hclose q hs) (by positivity))
  have hd : r⁻¹ ^ 2 • fderiv ℝ B p = fderiv ℝ A p := by
    rw [← fderiv_const_smul hB]
    exact heq.fderiv_eq
  have hnorm : r⁻¹ ^ 2 * ‖fderiv ℝ B p‖ ≤ 216 * ε * ‖T‖ ^ 3 := by
    have h := congrArg norm hd
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
    exact h.le.trans hA
  change ‖fderiv ℝ B p‖ ≤ _
  calc
    _ = r ^ 2 * (r⁻¹ ^ 2 * ‖fderiv ℝ B p‖) := by field_simp [hr.ne']
    _ ≤ r ^ 2 * (216 * ε * ‖T‖ ^ 3) := mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
    _ = _ := by ring

end PoincareConjecture.CylinderCover
