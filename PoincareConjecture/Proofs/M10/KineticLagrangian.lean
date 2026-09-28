import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M10

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem hasFDerivAt_quadratic_of_symmetric (B : Y →L[ℝ] Y →L[ℝ] ℝ)
    (hsym : ∀ v w : Y, B v w = B w v) (v : Y) :
    HasFDerivAt (fun w ↦ B w w) ((2 : ℝ) • B v) v := by
  have hd : HasFDerivAt (fun w : Y ↦ B w w) (B v + B.flip v) v := by
    simpa only [ContinuousLinearMap.comp_id, id_eq] using
      (B.hasFDerivAt.clm_apply (hasFDerivAt_id v))
  have heq : B v + B.flip v = (2 : ℝ) • B v := by
    ext w
    simp only [smul_apply, smul_eq_mul, add_apply, ContinuousLinearMap.flip_apply]
    rw [hsym w v]
    ring
  rwa [heq] at hd

noncomputable def kineticLagrangian (B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ)
    (R : Y × ℝ → ℝ) (a : ℝ × Y × Y) : ℝ :=
  Real.sqrt a.1 * (R (a.2.1, a.1) + B (a.2.1, a.1) a.2.2 a.2.2)

theorem kineticLagrangian_contDiffAt {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ}
    {R : Y × ℝ → ℝ} {a : ℝ × Y × Y} {k : ℕ∞ω}
    (hB : ContDiffAt ℝ k B (a.2.1, a.1))
    (hR : ContDiffAt ℝ k R (a.2.1, a.1)) (ht : 0 < a.1) :
    ContDiffAt ℝ k (kineticLagrangian B R) a := by
  have hcoords : ContDiffAt ℝ k (fun b : ℝ × Y × Y ↦ (b.2.1, b.1)) a :=
    contDiffAt_snd.fst.prodMk contDiffAt_fst
  exact (contDiffAt_fst.sqrt ht.ne').mul ((hR.comp a hcoords).add
    (((hB.comp a hcoords).clm_apply contDiffAt_snd.snd).clm_apply contDiffAt_snd.snd))

theorem kineticLagrangian_velocity_derivative {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ}
    {R : Y × ℝ → ℝ} {a : ℝ × Y × Y}
    (hL : DifferentiableAt ℝ (kineticLagrangian B R) a)
    (hsym : ∀ v w : Y, B (a.2.1, a.1) v w = B (a.2.1, a.1) w v) (w : Y) :
    fderiv ℝ (kineticLagrangian B R) a (0, 0, w) =
      2 * Real.sqrt a.1 * B (a.2.1, a.1) a.2.2 w := by
  let j : Y → ℝ × Y × Y := fun v ↦ (a.1, a.2.1, v)
  let j' : Y →L[ℝ] ℝ × Y × Y := (0 : Y →L[ℝ] ℝ).prod
    ((0 : Y →L[ℝ] Y).prod (ContinuousLinearMap.id ℝ Y))
  have hj : HasFDerivAt j j' a.2.2 :=
    (hasFDerivAt_const a.1 a.2.2).prodMk
      ((hasFDerivAt_const a.2.1 a.2.2).prodMk (hasFDerivAt_id a.2.2))
  have hc := hL.hasFDerivAt.comp (f := j) a.2.2 hj
  have hq := ((hasFDerivAt_const (R (a.2.1, a.1)) a.2.2).add
    (hasFDerivAt_quadratic_of_symmetric (B (a.2.1, a.1)) hsym a.2.2)).const_mul
      (Real.sqrt a.1)
  have hcalc := congrArg (fun D : Y →L[ℝ] ℝ ↦ D w) (hc.unique hq)
  simp only [j', ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul, zero_add] at hcalc
  calc
    _ = Real.sqrt a.1 * (2 * B (a.2.1, a.1) a.2.2 w) := hcalc
    _ = _ := by ring

end PoincareConjecture.M10
