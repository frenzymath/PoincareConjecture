import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceHorizontal
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64HorizontalSource_inverse_deriv {tau : ℝ ≃ₜ ℝ}
    (ht : Differentiable ℝ tau) (hi : Differentiable ℝ tau.symm) (x : ℝ) :
    deriv tau x * deriv tau.symm (tau x) = 1 := by
  have h := ((hi (tau x)).hasDerivAt.comp x (ht x).hasDerivAt).deriv
  have heq : (tau.symm ∘ tau : ℝ → ℝ) = id := by funext y; simp
  rw [heq, deriv_id] at h
  exact (mul_comm _ _).trans h.symm

theorem m64HorizontalSource_symm_strictMono {tau : ℝ ≃ₜ ℝ}
    (ht : StrictMono tau) : StrictMono tau.symm := by
  intro x y hxy
  exact ht.lt_iff_lt.mp (by simpa using hxy)

theorem m64HorizontalSource_interval_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {tau : ℝ ≃ₜ ℝ} (ht : Differentiable ℝ tau) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod) (f : ℝ → E) :
    (∫ x in Icc (0 : ℝ) curvePeriod, deriv tau x • f (tau x)) =
      ∫ x in Icc (0 : ℝ) curvePeriod, f x := by
  have h := integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Icc (0 : ℝ) curvePeriod) measurableSet_Icc
    (fun x _ => (ht x).hasDerivAt.hasDerivWithinAt) (hmono.monotone.monotoneOn _) f
  rw [tau.continuous.image_Icc_of_strictMono hmono, h0, hP] at h
  exact h.symm

theorem m64HorizontalSource_horizontal_green
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ ∞ tau) (hi : ContDiff ℝ ∞ tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod)
    (u V : LoopPlane → E) {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p • (deriv tau (p 0) • V (m64HorizontalSource tau p))) +
      (∫ p in S, fderiv ℝ phi p e0 • u (m64HorizontalSource tau p)) =
    (∫ p in S, (phi ∘ (m64HorizontalSource tau).symm) p • V p) +
      (∫ p in S, fderiv ℝ (phi ∘ (m64HorizontalSource tau).symm) p e0 • u p) := by
  let T := m64HorizontalSource tau
  let psi := phi ∘ T.symm
  have hpsi : ContDiff ℝ 1 psi := hp.comp
    (m64HorizontalSource_contDiff (hi.of_le (by simp)))
  have heq : psi ∘ T = phi := by funext p; simp [psi]
  have hd (p : LoopPlane) : deriv tau (p 0) * fderiv ℝ psi (T p) e0 =
      fderiv ℝ phi p e0 := by
    have h := m64HorizontalSource_fderiv_comp (ht.differentiable (by simp))
      (hpsi.differentiable (by simp)) p 0
    rw [heq] at h
    simpa only [ite_true, smul_eq_mul] using h.symm
  change _ = (∫ p in S, psi p • V p) + ∫ p in S, fderiv ℝ psi p e0 • u p
  congr 1
  · calc
      _ = ∫ p in S, deriv tau (p 0) • (psi (T p) • V (T p)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        simp only [psi, Function.comp_apply, Homeomorph.symm_apply_apply]
        exact smul_comm _ _ _
      _ = _ := m64HorizontalSource_integral (ht.differentiable (by simp))
        hpos hmono h0 hP (fun p => psi p • V p)
  · calc
      _ = ∫ p in S, deriv tau (p 0) • (fderiv ℝ psi (T p) e0 • u (T p)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        rw [← hd, mul_smul]
      _ = _ := m64HorizontalSource_integral (ht.differentiable (by simp))
        hpos hmono h0 hP (fun p => fderiv ℝ psi p e0 • u p)

def m64HorizontalSourceRadialTest (tau : ℝ ≃ₜ ℝ) (phi : LoopPlane → ℝ)
    (p : LoopPlane) : ℝ :=
  deriv tau.symm (p 0) * phi ((m64HorizontalSource tau).symm p)

theorem m64HorizontalSourceRadialTest_contDiff {tau : ℝ ≃ₜ ℝ}
    (hi : ContDiff ℝ ∞ tau.symm) {phi : LoopPlane → ℝ} {q : WithTop ℕ∞}
    (hp : ContDiff ℝ q phi) (hq : q ≤ ∞) :
    ContDiff ℝ q (m64HorizontalSourceRadialTest tau phi) := by
  have hid : ContDiff ℝ ∞ (deriv tau.symm) := (contDiff_infty_iff_deriv.mp hi).2
  exact ((hid.of_le hq).comp
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).contDiff).mul
      (hp.comp (m64HorizontalSource_contDiff (hi.of_le hq)))

theorem m64HorizontalSourceRadialTest_fderiv {tau : ℝ ≃ₜ ℝ}
    (hi : ContDiff ℝ ∞ tau.symm) {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (p : LoopPlane) :
    fderiv ℝ (m64HorizontalSourceRadialTest tau phi) p e1 =
      deriv tau.symm (p 0) * fderiv ℝ phi ((m64HorizontalSource tau).symm p) e1 := by
  let w := fun p : LoopPlane => deriv tau.symm (p 0)
  let psi := phi ∘ (m64HorizontalSource tau).symm
  have hid : ContDiff ℝ ∞ (deriv tau.symm) := (contDiff_infty_iff_deriv.mp hi).2
  have hw : Differentiable ℝ w := (hid.differentiable (by simp)).comp
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).differentiable
  have hpsi : Differentiable ℝ psi := (hp.differentiable (by simp)).comp
    ((m64HorizontalSource_contDiff hi).differentiable (by simp))
  have hw1 : fderiv ℝ w p e1 = 0 := by
    rw [show w = deriv tau.symm ∘ (EuclideanSpace.proj (0 : Fin 2)) from rfl,
      fderiv_comp p (hid.differentiable (by simp) _)
        (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).differentiableAt,
      ContinuousLinearMap.comp_apply,
      (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).fderiv]
    simp
  have hp1 := m64HorizontalSource_fderiv_comp (hi.differentiable (by simp))
    (hp.differentiable (by simp)) p 1
  change fderiv ℝ (w * psi) p e1 = _
  rw [fderiv_mul (hw p) (hpsi p), add_apply, smul_apply, smul_apply, hw1]
  simpa only [psi, m64HorizontalSource_symm, show (1 : Fin 2) ≠ 0 from by decide,
    ite_false, one_smul, smul_eq_mul, one_mul, mul_zero, add_zero, w] using
    congrArg (fun z : ℝ => deriv tau.symm (p 0) * z) hp1

theorem m64HorizontalSource_radial_green
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {tau : ℝ ≃ₜ ℝ} (ht : ContDiff ℝ ∞ tau) (hi : ContDiff ℝ ∞ tau.symm)
    (hpos : ∀ x, 0 < deriv tau x) (hmono : StrictMono tau)
    (h0 : tau 0 = 0) (hP : tau curvePeriod = curvePeriod)
    (u V : LoopPlane → E) {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p • V (m64HorizontalSource tau p)) +
      (∫ p in S, fderiv ℝ phi p e1 • u (m64HorizontalSource tau p)) =
    (∫ p in S, m64HorizontalSourceRadialTest tau phi p • V p) +
      (∫ p in S, fderiv ℝ (m64HorizontalSourceRadialTest tau phi) p e1 • u p) := by
  let T := m64HorizontalSource tau
  let psi := m64HorizontalSourceRadialTest tau phi
  have hinv := m64HorizontalSource_inverse_deriv (ht.differentiable (by simp))
    (hi.differentiable (by simp))
  have hv (p : LoopPlane) : deriv tau (p 0) * psi (T p) = phi p := by
    change deriv tau (p 0) *
      (deriv tau.symm (tau (p 0)) * phi (T.symm (T p))) = phi p
    rw [Homeomorph.symm_apply_apply, ← mul_assoc, hinv, one_mul]
  have hd (p : LoopPlane) : deriv tau (p 0) * fderiv ℝ psi (T p) e1 =
      fderiv ℝ phi p e1 := by
    rw [m64HorizontalSourceRadialTest_fderiv hi hp]
    change deriv tau (p 0) *
      (deriv tau.symm (tau (p 0)) * fderiv ℝ phi (T.symm (T p)) e1) = _
    rw [Homeomorph.symm_apply_apply, ← mul_assoc, hinv, one_mul]
  change _ = (∫ p in S, psi p • V p) + ∫ p in S, fderiv ℝ psi p e1 • u p
  congr 1
  · calc
      _ = ∫ p in S, deriv tau (p 0) • (psi (T p) • V (T p)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        rw [← hv, mul_smul]
      _ = _ := m64HorizontalSource_integral (ht.differentiable (by simp))
        hpos hmono h0 hP (fun p => psi p • V p)
  · calc
      _ = ∫ p in S, deriv tau (p 0) • (fderiv ℝ psi (T p) e1 • u (T p)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        rw [← hd, mul_smul]
      _ = _ := m64HorizontalSource_integral (ht.differentiable (by simp))
        hpos hmono h0 hP (fun p => fderiv ℝ psi p e1 • u p)

end PoincareConjecture
