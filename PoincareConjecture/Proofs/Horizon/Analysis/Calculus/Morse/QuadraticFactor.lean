import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.DividedDifferences
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus.Morse

universe u

variable {E V : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def quadraticFactor (f : E → V) (x : E) : E →L[ℝ] E →L[ℝ] V :=
  ∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ f) (t • x)

omit [CompleteSpace V] in
theorem contDiff_quadraticFactor [FiniteDimensional ℝ E]
    {f : E → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (quadraticFactor f) := by
  have : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] V) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] V)
  unfold quadraticFactor
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    hD.fderiv_right (by simp)
  apply Poincare.Analysis.contDiff_parameter_intervalIntegral_of_contDiff
    (F := fun q : E × ℝ => (1 - q.2) • fderiv ℝ (fderiv ℝ f) (q.2 • q.1))
  exact (contDiff_const.sub contDiff_snd).smul
    (hH.comp (contDiff_snd.smul contDiff_fst))

@[simp]
theorem quadraticFactor_zero (f : E → V) :
    quadraticFactor f 0 = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 := by
  simp only [quadraticFactor, smul_zero]
  rw [intervalIntegral.integral_smul_const (fun t : ℝ => 1 - t)
    (fderiv ℝ (fderiv ℝ f) 0)]
  congr 1
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
    intervalIntegrable_const
    (continuous_id.intervalIntegrable 0 1)]
  norm_num

omit [CompleteSpace V] in
theorem quadraticFactor_apply {f : E → V} (hf : ContDiff ℝ ∞ f) (x v w : E) :
    quadraticFactor f x v w =
      ∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ f) (t • x) v w := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hD.fderiv_right (by simp)
  have hc : Continuous
      (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ f) (t • x)) :=
    (continuous_const.sub continuous_id).smul
      (hH.continuous.comp (continuous_id.smul continuous_const))
  rw [quadraticFactor,
    ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1),
    ContinuousLinearMap.intervalIntegral_apply
      ((hc.clm_apply continuous_const).intervalIntegrable 0 1)]
  rfl

omit [CompleteSpace V] in
theorem quadraticFactor_symmetric {f : E → V}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    quadraticFactor f x v w = quadraticFactor f x w v := by
  rw [quadraticFactor_apply hf, quadraticFactor_apply hf]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [(hf.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)).eq v w]

theorem sub_eq_fderiv_add_quadraticFactor {f : E → V}
    (hf : ContDiff ℝ ∞ f) (x : E) :
    f x - f 0 = fderiv ℝ f 0 x + quadraticFactor f x x x := by
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hHf : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hDf.fderiv_right (by simp)
  let D : ℝ → V := fun t => fderiv ℝ f (t • x) x
  let H : ℝ → V := fun t => fderiv ℝ (fderiv ℝ f) (t • x) x x
  have hD (t : ℝ) : HasDerivAt D (H t) t := by
    have hd := ((hDf.differentiable (by simp))
      (t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    simpa [D, H] using hd.clm_apply (hasDerivAt_const t x)
  have hd (t : ℝ) : HasDerivAt
      (fun s => f (s • x) + (1 - s) • D s) ((1 - t) • H t) t := by
    have hdf := ((hf.differentiable (by simp))
      (t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    convert hdf.add (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).smul (hD t))
      using 1
    · rfl
    · simp [D]
  have hc : Continuous (fun t : ℝ => (1 - t) • H t) := by
    exact (continuous_const.sub continuous_id).smul
      (((hHf.continuous.comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const).clm_apply continuous_const)
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  have hB : quadraticFactor f x x x = ∫ t in (0 : ℝ)..1, (1 - t) • H t :=
    quadraticFactor_apply hf x x x
  rw [hB, heq]
  simp [D]
  abel

theorem eq_add_quadraticFactor_of_fderiv_eq_zero {f : E → V}
    (hf : ContDiff ℝ ∞ f) (hcrit : fderiv ℝ f 0 = 0) (x : E) :
    f x = f 0 + quadraticFactor f x x x := by
  have h := sub_eq_fderiv_add_quadraticFactor hf x
  rw [hcrit, zero_apply, zero_add] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

section RealValued

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem bilinear_eq_zero_of_diagonal_eq_zero (B : P →L[ℝ] P →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) (hdiag : ∀ v, B v v = 0) : B = 0 := by
  ext v w
  have h := hdiag (v + w)
  simp only [map_add, add_apply] at h
  rw [hdiag v, hdiag w, hsymm w v] at h
  simp only [zero_apply]
  linarith

theorem exists_hessian_diagonal_ne_zero [Nontrivial P] {f : P → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hinj : Function.Injective (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ v : P, fderiv ℝ (fderiv ℝ f) 0 v v ≠ 0 := by
  by_contra h
  push Not at h
  have hzero := bilinear_eq_zero_of_diagonal_eq_zero (fderiv ℝ (fderiv ℝ f) 0)
    (fun v w => (hf.contDiffAt.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)).eq v w) h
  obtain ⟨v, hv⟩ := exists_ne (0 : P)
  apply hv
  apply hinj
  rw [hzero]
  rfl

end RealValued

theorem exists_smooth_quadratic_factor
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcrit : fderiv ℝ f 0 = 0) :
    ∃ B : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ ∞ B ∧
      (∀ x v w, B x v w = B x w v) ∧
      B 0 = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 ∧
      ∀ x, f x = f 0 + B x x x := by
  exact ⟨quadraticFactor f, contDiff_quadraticFactor hf,
    quadraticFactor_symmetric hf, quadraticFactor_zero f,
    eq_add_quadraticFactor_of_fderiv_eq_zero hf hcrit⟩

end Poincare.Analysis.Calculus.Morse
