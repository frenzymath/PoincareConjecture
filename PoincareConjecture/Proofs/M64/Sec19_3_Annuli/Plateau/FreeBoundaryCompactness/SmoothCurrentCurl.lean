import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.CurrentStrongPairing
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessHolder
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "b" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)

theorem smooth_planar_current_curl
    (f : E → E) (hf : ContDiff ℝ ∞ f) (p : E) :
    fderiv ℝ (fun q => planarCircleCurrent (f q) (fderiv ℝ f q (b 1))) p (b 0) -
      fderiv ℝ (fun q => planarCircleCurrent (f q) (fderiv ℝ f q (b 0))) p (b 1) =
        2 * planarCircleCurrent (fderiv ℝ f p (b 0)) (fderiv ℝ f p (b 1)) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hder (i j : Fin 2) :
      fderiv ℝ (fun q => planarCurrentBilinear (f q) (fderiv ℝ f q (b i))) p (b j) =
        planarCurrentBilinear (f p) (fderiv ℝ (fderiv ℝ f) p (b j) (b i)) +
          planarCurrentBilinear (fderiv ℝ f p (b j)) (fderiv ℝ f p (b i)) := by
    have hi := ((hD.differentiable (by simp) p).hasFDerivAt).clm_apply
      (hasFDerivAt_const (b i) p)
    have h := (planarCurrentBilinear.hasFDerivAt.comp p
      ((hf.differentiable (by simp) p).hasFDerivAt)).clm_apply hi
    simp only [Function.comp_def] at h
    rw [h.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add]
  have hsymm := (hf.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) (b 0) (b 1)
  simp_rw [← planarCurrentBilinear_apply]
  rw [hder 1 0, hder 0 1, hsymm]
  simp only [planarCurrentBilinear_apply, planarCircleCurrent]
  ring

theorem smooth_planar_current_test_identity
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    {O : Set E} (hO : IsOpen O)
    (phi : E → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ O) :
    (∫ p in O, fderiv ℝ phi p (b 1) *
      planarCircleCurrent (f p) (fderiv ℝ f p (b 0))) -
    (∫ p in O, fderiv ℝ phi p (b 0) *
      planarCircleCurrent (f p) (fderiv ℝ f p (b 1))) =
      2 * ∫ p in O, phi p *
        planarCircleCurrent (fderiv ℝ f p (b 0)) (fderiv ℝ f p (b 1)) := by
  let J := fun (i : Fin 2) (p : E) =>
    planarCircleCurrent (f p) (fderiv ℝ f p (b i))
  have hJ (i : Fin 2) : ContDiff ℝ ∞ (J i) := by
    have h : ContDiff ℝ ∞ (fun q =>
        planarCurrentBilinear (f q) (fderiv ℝ f q (b i))) :=
      (planarCurrentBilinear.contDiff.comp hf).clm_apply
        ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
    simpa only [planarCurrentBilinear_apply] using h
  have h0 := HasWeakPartialDeriv.of_contDiff (i := (1 : Fin 2)) hO
    ((hJ 0).of_le (by simp)) phi hp hc hs
  have h1 := HasWeakPartialDeriv.of_contDiff (i := (0 : Fin 2)) hO
    ((hJ 1).of_le (by simp)) phi hp hc hs
  have hi (i j : Fin 2) : IntegrableOn (fun p => fderiv ℝ (J i) p (b j) * phi p) O := by
    apply Integrable.integrableOn
    exact ((((hJ i).continuous_fderiv (by simp)).clm_apply continuous_const).mul
      hp.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hid : (∫ p in O, fderiv ℝ (J 1) p (b 0) * phi p) -
      (∫ p in O, fderiv ℝ (J 0) p (b 1) * phi p) =
        2 * ∫ p in O, phi p *
          planarCircleCurrent (fderiv ℝ f p (b 0)) (fderiv ℝ f p (b 1)) := by
    rw [← integral_sub (hi 1 0) (hi 0 1), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    have h := smooth_planar_current_curl f hf p
    change fderiv ℝ (J 1) p (b 0) - fderiv ℝ (J 0) p (b 1) = _ at h
    have hh := congrArg (fun z : ℝ => z * phi p) h
    nlinarith [hh]
  change (∫ p in O, fderiv ℝ phi p (b 1) * J 0 p) -
      (∫ p in O, fderiv ℝ phi p (b 0) * J 1 p) = _
  simp only [mul_comm] at h0 h1 hid ⊢
  linarith

end PoincareConjecture.M64
