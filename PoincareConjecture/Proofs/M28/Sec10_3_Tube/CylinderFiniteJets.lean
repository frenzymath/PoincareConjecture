import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderScalarReadout
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.OrdinaryCoefficientJets











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.Proofs.M28.FiniteHessian
open PoincareConjecture.Proofs.M28.NeckAnalysis

private theorem hasUniformJetBoundsAt_cylinder_affine
    {ι : Type*} {n : ℕ} {f : ι → RoundCylinderCoordinates → ℝ} (s : ι → ℝ)
    (hf : HasUniformJetBoundsAt n f (fun i => (0, s i)))
    (hc : ∀ i, ContDiffAt ℝ ∞ (f i) (0, s i)) :
    HasUniformJetBoundsAt n (fun i => f i ∘ cylinderScalarCoordinates (s i))
      (fun _ => (0 : EuclideanSpace ℝ (Fin 3))) := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) →L[ℝ] RoundCylinderCoordinates) :=
    inferInstanceAs (NormedAddCommGroup
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) × ℝ))
  let L := cylinderScalarCoordinateEquiv.toContinuousLinearMap
  have hD (i : ι) : fderiv ℝ (cylinderScalarCoordinates (s i)) = fun _ => L := by
    funext x
    exact (cylinderScalarCoordinates_hasFDerivAt (s i) x).fderiv
  have hjD : HasUniformJetBoundsAt n
      (fun i => fderiv ℝ (cylinderScalarCoordinates (s i)))
      (fun _ => (0 : EuclideanSpace ℝ (Fin 3))) := by
    intro k _
    refine ⟨‖L‖, fun i => ?_⟩
    change ‖iteratedFDeriv ℝ k (fderiv ℝ (cylinderScalarCoordinates (s i))) 0‖ ≤ ‖L‖
    rw [hD i]
    cases k with
    | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
    | succ k =>
        rw [iteratedFDeriv_succ_const (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) k L]
        simpa only [Pi.zero_apply, norm_zero] using norm_nonneg L
  apply hjD.comp_of_fderiv
  · simpa only [cylinderScalarCoordinates_zero] using hf
  · exact fun i => (contDiff_cylinderScalarCoordinates (s i)).contDiffAt
  · simpa only [cylinderScalarCoordinates_zero] using hc





theorem hasUniformJetBoundsAt_cylinderNeckCoefficients
    {ι : Type*} {M : ι → Type u} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M i)]
    [∀ i, IsManifold (𝓡 3) ∞ (M i)]
    {g : ∀ i, RiemannianMetric 3 (M i)} (N : ∀ i, EpsilonNeck (g i))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1)
    (heq : ∀ i, (N i).epsilon = epsilon) (m : ℕ) (hm : m ≤ ⌊epsilon⁻¹⌋₊)
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    HasUniformJetBoundsAt m (fun i => cylinderNeckCoefficients (N i) (q i) (s i))
      (fun _ => (0 : EuclideanSpace ℝ (Fin 3))) := by
  have hsN (i : ι) : s i ∈ Ioo (-(N i).epsilon⁻¹) (N i).epsilon⁻¹ := by
    simpa only [heq i] using hs i
  have hc (i : ι) : ContDiffAt ℝ ∞
      (cylinderNeckCoefficients (N i) (q i) (s i)) 0 :=
    (contDiffOn_cylinderNeckCoefficients (N i) (q i) (s i)).contDiffAt
      ((isOpen_cylinderNeckChartDomain (N i) (q i) (s i)).mem_nhds
        (zero_mem_cylinderNeckChartDomain (N i) (q i) (hsN i)))
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  apply HasUniformJetBoundsAt.of_basis b
  · intro a
    apply HasUniformJetBoundsAt.of_basis b
    · intro c
      let B : ι → RoundCylinderTwoTensor := fun i z v w =>
        (N i).scale⁻¹ ^ 2 * roundCylinderPullback (g i) (N i).coordinate_map z v w
      have hB (i : ι) : RoundCylinderClose epsilon 0 (B i) := by
        simpa only [heq i] using (N i).metric_comparison.close
      have hj := hasUniformJetBoundsAt_cylinder_coefficients_of_close
        hepsilon hsmall m hm q s hs B hB a c
      have hraw (i : ι) : ContDiffAt ℝ ∞ (fun p => roundCylinderTensorCoefficient
          (B i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) p a c) (0, s i) := by
        apply ((hB i).1 (q i) a c).contDiffAt
        apply ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).open_target.prod
          isOpen_Ioo).mem_nhds
        refine ⟨?_, hs i⟩
        rw [← sphere_chart_center (q i)]
        exact (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).map_source
          (mem_chart_source _ (q i))
      apply (hasUniformJetBoundsAt_cylinder_affine s hj hraw).congr_germ
      exact fun i => (cylinderNeckCoefficients_frozen_germ (N i) (q i) (hsN i) a c).symm
    · exact fun i c => ((hc i).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  · exact fun i a => (hc i).clm_apply contDiffAt_const

end PoincareConjecture.M28.tube
