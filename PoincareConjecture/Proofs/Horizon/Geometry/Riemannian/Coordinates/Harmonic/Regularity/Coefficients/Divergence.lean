import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Derivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.FrozenPositiveDefinite
import Mathlib.Analysis.Calculus.Gradient.Basic

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}

theorem euclidean_gradient_component (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    _root_.gradient f x i = fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
    (x := EuclideanSpace.basisFun (Fin n) ℝ i) (y := fderiv ℝ f x)
  simpa only [gradient, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] using h

theorem contDiff_euclidean_gradient {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (_root_.gradient f) := by
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.contDiff.comp
    (hf.fderiv_right (by simp))

theorem lapEval_fderiv_eq_divergence_gradient {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin n)) :
    Poincare.Parabolic.Interior.Kernel.lapEval (fderiv ℝ (fderiv ℝ f) x) =
      ∑ i, fderiv ℝ (fun y => _root_.gradient f y i) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [Poincare.Parabolic.Interior.Kernel.lapEval_basis (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [euclidean_gradient_component]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h := (hdf.differentiable (by simp) x).hasFDerivAt
  have heval := (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.basisFun (Fin n) ℝ i)).hasFDerivAt.comp x h
  exact (congrArg (fun L => L (EuclideanSpace.basisFun (Fin n) ℝ i)) heval.fderiv).symm

end PoincareConjecture.HarmonicCoordinates

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem divergenceOperator_gradient (D : LeviCivitaData g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    g.euclideanDivergenceOperator x (_root_.gradient f x) =
      g.pullbackVolumeDensity id x • D.gradient f x := by
  have hdual : innerSL ℝ (_root_.gradient f x) = fderiv ℝ f x := toDual_gradient
  have hg : D.gradient f x = (g.euclideanCoefficients x).inverse (fderiv ℝ f x) := by
    unfold LeviCivitaData.gradient
    have hm : mvfderiv (𝓡 n) f x = fderiv ℝ f x := by
      ext v
      simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
      rfl
    rw [hm]
    rfl
  simp only [RiemannianMetric.euclideanDivergenceOperator, smul_apply,
    ContinuousLinearMap.comp_apply, hdual, hg]

theorem density_mul_laplacian_eq_divergenceOperator (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    g.pullbackVolumeDensity id x * D.laplacian f x =
      ∑ i, fderiv ℝ (fun y =>
        (g.euclideanDivergenceOperator y (_root_.gradient f y)) i) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [D.density_mul_laplacian_eq_divergence (hf.contDiffAt)]
  simp only [D.divergenceOperator_gradient]
  rfl

theorem lapEval_fderiv_eq_metric_add_divergence (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    Poincare.Parabolic.Interior.Kernel.lapEval (fderiv ℝ (fderiv ℝ f) x) =
      g.pullbackVolumeDensity id x * D.laplacian f x +
        ∑ i, fderiv ℝ (fun y =>
          ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
            g.euclideanDivergenceOperator y) (_root_.gradient f y)) i) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hgrad := HarmonicCoordinates.contDiff_euclidean_gradient hf
  have hflux := g.contDiff_euclideanDivergenceOperator.clm_apply hgrad
  have hdiff (i : Fin n) :
      fderiv ℝ (fun y =>
        ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
          g.euclideanDivergenceOperator y) (_root_.gradient f y)) i) x =
        fderiv ℝ (fun y => _root_.gradient f y i) x -
          fderiv ℝ (fun y =>
            (g.euclideanDivergenceOperator y (_root_.gradient f y)) i) x := by
    have hg := ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hgrad).differentiable (by simp) x
    have ha := ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hflux).differentiable (by simp) x
    simpa only [sub_apply, ContinuousLinearMap.id_apply, PiLp.sub_apply,
      Function.comp_def, EuclideanSpace.coe_proj] using fderiv_fun_sub hg ha
  rw [HarmonicCoordinates.lapEval_fderiv_eq_divergence_gradient hf,
    D.density_mul_laplacian_eq_divergenceOperator hf]
  simp_rw [hdiff, sub_apply]
  rw [Finset.sum_sub_distrib]
  ring

end PoincareConjecture.LeviCivitaData
