import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryZeroExtension












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture





theorem m64ZeroTrace_boundaryReflect_weak {u v : LoopPlane → ℝ} (i : Fin 2)
    (hu : Continuous u) (hzero : ∀ p : LoopPlane, p 0 = 0 → u p = 0)
    (huLp : MemLp u 2 (volume.restrict (halfSpace 2)))
    (hvLp : MemLp v 2 (volume.restrict (halfSpace 2)))
    (hw : HasWeakPartialDeriv i v u (halfSpace 2)) (epsilon : ℝ) :
    HasWeakPartialDeriv i (m64BoundaryReflect (epsilon * coordinateSign i) v)
      (m64BoundaryReflect epsilon u) univ := by
  intro phi hp hc _
  let psi : LoopPlane → ℝ := fun p => phi p + (epsilon * coordinateSign i) * phi (reflect p)
  have hps : ContDiff ℝ ∞ psi := hp.add
    (contDiff_const.mul (hp.comp reflect.toContinuousLinearEquiv.contDiff))
  have hpc : HasCompactSupport psi := hc.add
    (hc.comp_homeomorph reflect.toHomeomorph).mul_left
  have hderiv (p : LoopPlane) :
      fderiv ℝ psi p (EuclideanSpace.single i 1) =
        fderiv ℝ phi p (EuclideanSpace.single i 1) +
          epsilon * fderiv ℝ phi (reflect p) (EuclideanSpace.single i 1) := by
    rw [m64Boundary_reflected_test_partial hp (epsilon * coordinateSign i) p i]
    by_cases hi : i = 0 <;> simp [coordinateSign, hi]
  simp only [Measure.restrict_univ]
  rw [m64BoundaryReflect_integral huLp
    ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ _) epsilon,
    m64BoundaryReflect_integral hvLp hp.continuous hc (epsilon * coordinateSign i)]
  convert m64Continuous_zeroTrace_weak_test i hu hzero huLp hvLp hw hps hpc using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by dsimp only; rw [hderiv]





theorem m64OddBoundaryReflect_weak {u v : LoopPlane → ℝ} (i : Fin 2)
    (hu : Continuous u) (hzero : ∀ p : LoopPlane, p 0 = 0 → u p = 0)
    (huLp : MemLp u 2 (volume.restrict (halfSpace 2)))
    (hvLp : MemLp v 2 (volume.restrict (halfSpace 2)))
    (hw : HasWeakPartialDeriv i v u (halfSpace 2)) :
    HasWeakPartialDeriv i (m64BoundaryReflect (-coordinateSign i) v)
      (m64ContinuousBoundaryReflect (-1) u) univ := by
  have hh := m64ZeroTrace_boundaryReflect_weak i hu hzero huLp hvLp hw (-1)
  have hae : m64ContinuousBoundaryReflect (-1) u =ᵐ[volume.restrict univ]
      m64BoundaryReflect (-1) u := by
    simpa only [Measure.restrict_univ] using m64ContinuousBoundaryReflect_ae (-1) u
  simpa only [neg_one_mul] using M60.suWeakPartial_congr_ae hh hae EventuallyEq.rfl

end PoincareConjecture
