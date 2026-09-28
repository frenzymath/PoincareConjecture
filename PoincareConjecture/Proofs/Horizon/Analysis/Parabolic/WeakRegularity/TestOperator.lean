import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.ForwardEquation


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}



def diffusionTest
    (a : Fin n → Fin n → Spacetime n → ℝ) (b : Fin n → Spacetime n → ℝ)
    (φ : Spacetime n → ℝ) (z : Spacetime n) : ℝ :=
  -timeDeriv φ z - (∑ i, ∑ j, a i j z * spatialDeriv j (spatialDeriv i φ) z) -
    ∑ i, b i z * spatialDeriv i φ z

theorem diffusionTest_add
    (a : Fin n → Fin n → Spacetime n → ℝ) (b : Fin n → Spacetime n → ℝ)
    {φ ψ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) :
    diffusionTest a b (fun z => φ z + ψ z) =
      fun z => diffusionTest a b φ z + diffusionTest a b ψ z := by
  have hs (i) : spatialDeriv i (fun z => φ z + ψ z) =
      fun z => spatialDeriv i φ z + spatialDeriv i ψ z := by
    funext z
    simp only [spatialDeriv, fderiv_fun_add (hφ.differentiable (by simp) z)
      (hψ.differentiable (by simp) z), add_apply]
  have hss (i j) (z) : spatialDeriv j (spatialDeriv i (fun y => φ y + ψ y)) z =
      spatialDeriv j (spatialDeriv i φ) z + spatialDeriv j (spatialDeriv i ψ) z := by
    rw [hs]
    have hdφ : ContDiff ℝ ∞ (spatialDeriv i φ) :=
      (hφ.fderiv_right (by simp)).clm_apply contDiff_const
    have hdψ : ContDiff ℝ ∞ (spatialDeriv i ψ) :=
      (hψ.fderiv_right (by simp)).clm_apply contDiff_const
    change fderiv ℝ (fun y => spatialDeriv i φ y + spatialDeriv i ψ y) z
      (spatialDirection j) = _
    rw [fderiv_fun_add (hdφ.differentiable (by simp) z)
      (hdψ.differentiable (by simp) z)]
    rfl
  have ht (z) : timeDeriv (fun y => φ y + ψ y) z = timeDeriv φ z + timeDeriv ψ z := by
    simp only [timeDeriv, fderiv_fun_add (hφ.differentiable (by simp) z)
      (hψ.differentiable (by simp) z), add_apply]
  funext z
  simp only [diffusionTest, ht, hss]
  simp only [hs, mul_add, Finset.sum_add_distrib]
  ring

theorem diffusionTest_eq_zero_of_notMem_tsupport
    (a : Fin n → Fin n → Spacetime n → ℝ) (b : Fin n → Spacetime n → ℝ)
    (φ : Spacetime n → ℝ) {z : Spacetime n} (hz : z ∉ tsupport φ) :
    diffusionTest a b φ z = 0 := by
  have ht : timeDeriv φ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_apply_subset ℝ (0, 1) h))
  have hs (i) : spatialDeriv i φ z = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hz (tsupport_fderiv_apply_subset ℝ (spatialDirection i) h))
  have hss (i j) : spatialDeriv j (spatialDeriv i φ) z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz
      (tsupport_fderiv_apply_subset ℝ (spatialDirection i)
        (tsupport_fderiv_apply_subset ℝ (spatialDirection j) h)))
  simp only [diffusionTest, ht, hs, hss, mul_zero, Finset.sum_const_zero,
    neg_zero, sub_zero]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
