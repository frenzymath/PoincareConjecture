import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.AnnulusJoin
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularCap
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture

noncomputable def m64RadialLinear (c : ℝ) : LoopPlane →L[ℝ] LoopPlane :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).smulRight
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).smulRight
      (c • EuclideanSpace.basisFun (Fin 2) ℝ 1)

noncomputable def m64RadialAffine (c d : ℝ) (p : LoopPlane) : LoopPlane :=
  annulusPoint (p 0) (c * p 1 + d)

theorem m64RadialAffine_eq (c d : ℝ) (p : LoopPlane) :
    m64RadialAffine c d p = m64RadialLinear c p + annulusPoint 0 d := by
  ext i
  fin_cases i <;>
    simp [m64RadialAffine, m64RadialLinear, annulusPoint, EuclideanSpace.basisFun_apply]
  ring

theorem m64RadialAffine_hasFDerivAt (c d : ℝ) (p : LoopPlane) :
    HasFDerivAt (m64RadialAffine c d) (m64RadialLinear c) p := by
  have heq : m64RadialAffine c d = fun p => m64RadialLinear c p + annulusPoint 0 d :=
    funext (m64RadialAffine_eq c d)
  rw [heq]
  exact (m64RadialLinear c).hasFDerivAt.add_const _

theorem m64RadialLinear_det (c : ℝ) : (m64RadialLinear c).det = c := by
  unfold ContinuousLinearMap.det
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, m64RadialLinear, EuclideanSpace.basisFun_apply]

theorem m64RadialAffine_inverse {c : ℝ} (hc : c ≠ 0) (d : ℝ) (p : LoopPlane) :
    m64RadialAffine c⁻¹ (-d / c) (m64RadialAffine c d p) = p := by
  ext i
  fin_cases i <;> simp [m64RadialAffine, annulusPoint]
  field_simp
  ring

theorem m64RadialAffine_inverse' {c : ℝ} (hc : c ≠ 0) (d : ℝ) (p : LoopPlane) :
    m64RadialAffine c d (m64RadialAffine c⁻¹ (-d / c) p) = p := by
  ext i
  fin_cases i <;> simp [m64RadialAffine, annulusPoint]
  field_simp
  ring

theorem m64RadialAffine_injective {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    Function.Injective (m64RadialAffine c d) :=
  Function.LeftInverse.injective (m64RadialAffine_inverse hc d)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64AreaDensity_comp_radialAffine (g : RiemannianMetric n M)
    (f : LoopPlane → M) {c : ℝ} (hc : c ≠ 0) (d : ℝ) (p : LoopPlane) :
    m60AreaDensity g (f ∘ m64RadialAffine c d) p =
      |c| * m60AreaDensity g f (m64RadialAffine c d p) := by
  by_cases hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (m64RadialAffine c d p)
  · have h := M60.suAreaDensity_comp_plane g hf
      (m64RadialAffine_hasFDerivAt c d p).differentiableAt
    simpa only [(m64RadialAffine_hasFDerivAt c d p).fderiv, m64RadialLinear_det] using h
  · have hcomp : ¬MDifferentiableAt (𝓡 2) (𝓡 n) (f ∘ m64RadialAffine c d) p := by
      intro h
      have hback := h.comp_of_eq (m64RadialAffine c d p)
        (m64RadialAffine_hasFDerivAt c⁻¹ (-d / c)
          (m64RadialAffine c d p)).hasMFDerivAt.mdifferentiableAt
        (m64RadialAffine_inverse hc d p)
      have hfun : (f ∘ m64RadialAffine c d) ∘ m64RadialAffine c⁻¹ (-d / c) = f := by
        funext x
        exact congrArg f (m64RadialAffine_inverse' hc d x)
      exact hf (hfun ▸ hback)
    have hzero {h : LoopPlane → M} {z : LoopPlane}
        (hh : ¬MDifferentiableAt (𝓡 2) (𝓡 n) h z) : m60AreaDensity g h z = 0 := by
      have hgram : m60AreaGram g h z = 0 := by
        ext i j
        simp only [m60AreaGram, mfderiv_zero_of_not_mdifferentiableAt hh]
        change g.inner (h z) 0 0 = 0
        simp
      simp [m60AreaDensity, hgram]
    rw [hzero hf, hzero hcomp, mul_zero]

theorem m64AreaIntegral_comp_radialAffine (g : RiemannianMetric n M)
    (f : LoopPlane → M) {c : ℝ} (hc : c ≠ 0) (d : ℝ)
    {S : Set LoopPlane} (hS : MeasurableSet S) :
    (∫ p in S, m60AreaDensity g (f ∘ m64RadialAffine c d) p) =
      ∫ p in m64RadialAffine c d '' S, m60AreaDensity g f p := by
  simp_rw [m64AreaDensity_comp_radialAffine g f hc d]
  symm
  simpa only [m64RadialLinear_det, smul_eq_mul] using
    integral_image_eq_integral_abs_det_fderiv_smul volume hS
      (fun p _ => (m64RadialAffine_hasFDerivAt c d p).hasFDerivWithinAt)
      (m64RadialAffine_injective hc d).injOn (m60AreaDensity g f)

end PoincareConjecture
