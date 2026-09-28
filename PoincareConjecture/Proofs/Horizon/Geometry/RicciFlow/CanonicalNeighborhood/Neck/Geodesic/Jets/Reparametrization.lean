import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Coefficients

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

theorem quadratic_lower_rechart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] ℝ) {r : ℝ}
    (hB : ∀ w, (r ^ 2 / 2) * ‖w‖ ^ 2 ≤ B w w) (v : F) :
    ((2 * (max 1 ‖e.toContinuousLinearMap‖) ^ 2)⁻¹ * r ^ 2) * ‖v‖ ^ 2 ≤
      B.bilinearComp e.symm.toContinuousLinearMap e.symm.toContinuousLinearMap v v := by
  let A := max 1 ‖e.toContinuousLinearMap‖
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hv : ‖v‖ ≤ A * ‖e.symm v‖ := by
    calc
      ‖v‖ = ‖e (e.symm v)‖ := by rw [e.apply_symm_apply]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖e.symm v‖ := e.toContinuousLinearMap.le_opNorm _
      _ ≤ A * ‖e.symm v‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hvsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA.le (norm_nonneg _))).mpr hv
  calc
    _ ≤ ((2 * A ^ 2)⁻¹ * r ^ 2) * (A * ‖e.symm v‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hvsq (by positivity)
    _ = (r ^ 2 / 2) * ‖e.symm v‖ ^ 2 := by field_simp
    _ ≤ B (e.symm v) (e.symm v) := hB _

theorem RiemannianMetric.parametrizedCoefficients_comp_linear
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : RiemannianMetric n M) {f : E → M} (T : F →L[ℝ] E) {x : F}
    (hf : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) f (T x)) :
    g.parametrizedCoefficients (f ∘ T) x =
      (g.parametrizedCoefficients f (T x)).bilinearComp T T := by
  ext v w
  simp only [RiemannianMetric.parametrizedCoefficients_apply,
    ContinuousLinearMap.bilinearComp_apply, Function.comp_apply]
  rw [mfderiv_comp x hf T.mdifferentiableAt, T.mfderiv_eq]
  rfl

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem norm_fderiv_centeredParametrization_rechart_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (e : RoundCylinderCoordinates ≃L[ℝ] E) :
    ‖fderiv ℝ (g.parametrizedCoefficients
      (N.centeredParametrization q ∘ e.symm)) (e (0, s))‖ ≤
      216 * N.epsilon * N.scale ^ 2 * ‖e.symm.toContinuousLinearMap‖ ^ 3 := by
  let T : E →L[ℝ] RoundCylinderCoordinates := e.symm.toContinuousLinearMap
  let p := e (0, s)
  let B := g.parametrizedCoefficients (N.centeredParametrization q ∘ T)
  let A := fun y => (N.normalizedCenteredCoefficients q (T y)).bilinearComp T T
  have hp : T p = (0, s) := e.symm_apply_apply _
  have hB : DifferentiableAt ℝ B p := by
    apply (g.contDiffAt_parametrizedCoefficients ?_).differentiableAt (by simp)
    apply (N.centeredParametrization_contMDiffAt q (y := T p) ?_).comp p T.contMDiff.contMDiffAt
    simpa only [hp] using hs
  have heq : (fun y => N.scale⁻¹ ^ 2 • B y) =ᶠ[𝓝 p] A := by
    have hnear : ∀ᶠ y in 𝓝 p, (T y).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      (continuous_snd.comp T.continuous).continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (by simpa only [Function.comp_apply, hp] using hs))
    filter_upwards [hnear] with y hy
    dsimp only [B, A]
    rw [g.parametrizedCoefficients_comp_linear T
      ((N.centeredParametrization_contMDiffAt q hy).mdifferentiableAt (by simp))]
    ext v w
    rfl
  have hA : ‖fderiv ℝ A p‖ ≤ 216 * N.epsilon * ‖T‖ ^ 3 := by
    have hdiff : DifferentiableAt ℝ (N.normalizedCenteredCoefficients q) (T p) := by
      rw [hp]
      exact (N.normalizedCenteredCoefficients_contDiffAt q (y := (0, s)) hs).differentiableAt (by simp)
    have h := norm_fderiv_bilinearComp_linear_le T hdiff
    rw [hp] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (N.norm_fderiv_normalizedCenteredCoefficients_le q hs) (by positivity))
  have hd : N.scale⁻¹ ^ 2 • fderiv ℝ B p = fderiv ℝ A p := by
    rw [← fderiv_const_smul hB]
    exact heq.fderiv_eq
  have hnorm : N.scale⁻¹ ^ 2 * ‖fderiv ℝ B p‖ ≤ 216 * N.epsilon * ‖T‖ ^ 3 := by
    have h := congrArg norm hd
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
    exact h.le.trans hA
  change ‖fderiv ℝ B p‖ ≤ _
  calc
    _ = N.scale ^ 2 * (N.scale⁻¹ ^ 2 * ‖fderiv ℝ B p‖) := by
      field_simp [N.scale_pos.ne']
    _ ≤ N.scale ^ 2 * (216 * N.epsilon * ‖T‖ ^ 3) :=
      mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
    _ = _ := by ring

end EpsilonNeck
end PoincareConjecture
