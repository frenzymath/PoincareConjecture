

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace Poincare.ODE.Parameter

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def parameterFDeriv (f : ℝ × P → F) (z : ℝ × P) : P →L[ℝ] F :=
  (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ P)

def timeFDeriv (f : ℝ × P → F) (z : ℝ × P) : F := fderiv ℝ f z (1, 0)

theorem parameterFDeriv_eq_slice {f : ℝ × P → F} {t : ℝ} {p : P}
    (hf : DifferentiableAt ℝ f (t, p)) :
    parameterFDeriv f (t, p) = fderiv ℝ (fun q => f (t, q)) p := by
  exact (hf.hasFDerivAt.comp p (hasFDerivAt_prodMk_right t p)).fderiv.symm

theorem timeFDeriv_eq_slice {f : ℝ × P → F} {t : ℝ} {p : P}
    (hf : DifferentiableAt ℝ f (t, p)) :
    timeFDeriv f (t, p) = deriv (fun s => f (s, p)) t := by
  convert (hf.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t p)).hasDerivAt.deriv.symm
    using 1 <;> rfl

theorem hasDerivAt_parameterFDeriv {f : ℝ × P → F} {t : ℝ} {p : P}
    (hf : ContDiffAt ℝ 2 f (t, p)) :
    HasDerivAt (fun s => parameterFDeriv f (s, p))
      (parameterFDeriv (timeFDeriv f) (t, p)) t := by
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (t, p)) (t, p) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hP := hD.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inr ℝ ℝ P) (t, p))
  have hT := hD.clm_apply (hasFDerivAt_const (1, (0 : P)) (t, p))
  have htime : fderiv ℝ (timeFDeriv f) (t, p) =
      (fderiv ℝ (fderiv ℝ f) (t, p)).flip (1, 0) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (1, 0)) (t, p) = _
    simpa using hT.fderiv
  have h := (hP.comp t (hasFDerivAt_prodMk_left t p)).hasDerivAt
  convert h using 1 <;> try rfl
  rw [parameterFDeriv, htime]
  ext v
  simpa using (hf.isSymmSndFDerivAt (by norm_num)).eq (0, v) (1, 0)

theorem contDiffOn_parameterFDeriv {f : ℝ × P → F} {W : Set (ℝ × P)}
    (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) :
    ContDiffOn ℝ ∞ (parameterFDeriv f) W := by
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hW).mp hf).2.clm_comp contDiffOn_const

theorem hasDerivAt_parameterFDeriv_of_ode
    {f b : ℝ × P → F} {A : ℝ × P → F →L[ℝ] F} {W : Set (ℝ × P)}
    (hW : IsOpen W) (hf : ContDiffOn ℝ 2 f W) {t : ℝ} {p : P}
    (hz : (t, p) ∈ W) (hA : DifferentiableAt ℝ A (t, p))
    (hb : DifferentiableAt ℝ b (t, p))
    (hode : ∀ z ∈ W, timeFDeriv f z = A z (f z) + b z) :
    HasDerivAt (fun s => parameterFDeriv f (s, p))
      ((A (t, p)).comp (parameterFDeriv f (t, p)) +
        (parameterFDeriv A (t, p)).flip (f (t, p)) + parameterFDeriv b (t, p)) t := by
  have hfz := (hf (t, p) hz).contDiffAt (hW.mem_nhds hz)
  have heq : timeFDeriv f =ᶠ[𝓝 (t, p)] fun z => A z (f z) + b z := by
    filter_upwards [hW.mem_nhds hz] with z hz
    exact hode z hz
  have hprod : HasFDerivAt (fun z => A z (f z) + b z)
      ((A (t, p)).comp (fderiv ℝ f (t, p)) +
        (fderiv ℝ A (t, p)).flip (f (t, p)) + fderiv ℝ b (t, p)) (t, p) :=
    (hA.hasFDerivAt.clm_apply
      (hfz.differentiableAt (by norm_num)).hasFDerivAt).add hb.hasFDerivAt
  have hderiv := (hasDerivAt_parameterFDeriv hfz)
  apply hderiv.congr_deriv
  unfold parameterFDeriv
  rw [heq.fderiv_eq, hprod.fderiv]
  ext v
  simp

end Poincare.ODE.Parameter
