import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.AngularTangent
import PoincareConjecture.Definitions.Ch19.CurveEvolution
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

omit [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] in
private theorem periodic_eq_of_angle_eq (c : ℝ → M) (hp : Function.Periodic c curvePeriod)
    {x y : ℝ} (hxy : (x : Real.Angle) = y) : c x = c y := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hxy
  have heq : x = y + (k : ℝ) * curvePeriod := by
    unfold curvePeriod
    nlinarith
  rw [heq]
  exact hp.int_mul k y

omit [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] in
private theorem periodic_arg_local (c : ℝ → M) (hp : Function.Periodic c curvePeriod)
    {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    c w.arg = c (z.arg + (w / z).arg) := by
  apply periodic_eq_of_angle_eq c hp
  rw [Real.Angle.coe_add, Complex.arg_div_coe_angle hw hz]
  abel

omit [IsManifold (𝓡 3) ∞ M] in
private theorem periodic_arg_contMDiffAt (c : ℝ → M)
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 c) (hp : Function.Periodic c curvePeriod)
    {z : ℂ} (hz : z ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 3) 1 (fun w : ℂ => c w.arg) z := by
  have hslit : z / z ∈ Complex.slitPlane := by simp [div_self hz]
  have hlog : ContDiffAt ℝ 1 Complex.log (z / z) :=
    (Complex.contDiffAt_log hslit).restrict_scalars ℝ
  have hdiv : ContDiffAt ℝ 1 (fun w : ℂ => w / z) z :=
    (contDiff_id.div_const z).contDiffAt
  have hcomp : ContDiffAt ℝ 1 (fun w : ℂ => Complex.log (w / z)) z :=
    hlog.comp (f := fun w : ℂ => w / z) z hdiv
  have hangle : ContDiffAt ℝ 1 (fun w : ℂ => z.arg + (w / z).arg) z := by
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
      (contDiffAt_const (c := z.arg)).add (Complex.imCLM.contDiff.contDiffAt.comp z hcomp)
  apply (hc.contMDiffAt.comp z hangle.contMDiffAt).congr_of_eventuallyEq
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
  exact periodic_arg_local c hp hz hw




noncomputable def m65PeriodicLoopExtension (c : ℝ → M) (z : LoopPlane) : M :=
  c (Complex.orthonormalBasisOneI.repr.symm z).arg

omit [IsManifold (𝓡 3) ∞ M] in


theorem m65PeriodicLoopExtension_contMDiffOn (c : ℝ → M)
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 c) (hp : Function.Periodic c curvePeriod) :
    ContMDiffOn (𝓡 2) (𝓡 3) 1 (m65PeriodicLoopExtension c) loopAnnulus := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro heq
    have hpos := hz.1
    norm_num [heq] at hpos
  have hcomplex : Complex.orthonormalBasisOneI.repr.symm z ≠ 0 := by
    exact fun hzero => hz0 (Complex.orthonormalBasisOneI.repr.symm.map_eq_zero_iff.mp hzero)
  exact ((periodic_arg_contMDiffAt c hc hp hcomplex).comp z
    Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffAt
      ).contMDiffWithinAt



noncomputable def m65LoopOfPeriodic (c : ℝ → M)
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 c) (hp : Function.Periodic c curvePeriod) :
    C1FreeLoopSpace (M := M) :=
  loopOfExtension (m65PeriodicLoopExtension c) (m65PeriodicLoopExtension_contMDiffOn c hc hp)



theorem m65PeriodicFreeLoop_loopOfPeriodic (c : ℝ → M)
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 c) (hp : Function.Periodic c curvePeriod)
    (x : ℝ) : periodicFreeLoop (m65LoopOfPeriodic c hc hp) x = c x := by
  change c (Complex.orthonormalBasisOneI.repr.symm (angularPoint x)).arg = c x
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  apply periodic_eq_of_angle_eq c hp
  simpa only [angularPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.Angle.cos_coe, Real.Angle.sin_coe] using
    Complex.arg_cos_add_sin_mul_I_coe_angle (x : Real.Angle)

end PoincareConjecture
