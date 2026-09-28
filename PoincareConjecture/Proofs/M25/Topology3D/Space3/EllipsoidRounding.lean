import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def ellipsoidRadialRatio (A : E ≃L[ℝ] E) (y : E) : ℝ :=
  ‖A.symm y‖ / ‖y‖

theorem ellipsoidRadialRatio_pos (A : E ≃L[ℝ] E) {y : E} (hy : y ≠ 0) :
    0 < ellipsoidRadialRatio A y := by
  exact div_pos (norm_pos_iff.mpr (A.symm.map_ne_zero_iff.mpr hy)) (norm_pos_iff.mpr hy)

theorem ellipsoidRadialRatio_smul (A : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a) (y : E) :
    ellipsoidRadialRatio A (a • y) = ellipsoidRadialRatio A y := by
  simp only [ellipsoidRadialRatio, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  exact mul_div_mul_left _ _ ha.ne'

theorem ellipsoidRadialRatio_contDiffOn (A : E ≃L[ℝ] E) :
    ContDiffOn ℝ ∞ (ellipsoidRadialRatio A) ({0}ᶜ : Set E) := by
  intro y hy
  have hy0 : y ≠ 0 := hy
  exact ((A.symm.contDiff.contDiffAt.norm ℝ (A.symm.map_ne_zero_iff.mpr hy0)).div
    (contDiffAt_norm ℝ hy0) (norm_ne_zero_iff.mpr hy0)).contDiffWithinAt

noncomputable def ellipsoidRoundingField (A : E ≃L[ℝ] E) (y : E) : E :=
  Real.log (ellipsoidRadialRatio A y) • y

theorem ellipsoidRoundingField_contDiffOn (A : E ≃L[ℝ] E) :
    ContDiffOn ℝ ∞ (ellipsoidRoundingField A) ({0}ᶜ : Set E) := by
  exact ((ellipsoidRadialRatio_contDiffOn A).log
    (fun y hy => (ellipsoidRadialRatio_pos A hy).ne')).smul contDiff_id.contDiffOn

noncomputable def ellipsoidRoundingTrack (A : E ≃L[ℝ] E) (t : ℝ) (y : E) : E :=
  Real.exp (t * Real.log (ellipsoidRadialRatio A y)) • y

theorem ellipsoidRoundingTrack_zero (A : E ≃L[ℝ] E) (y : E) :
    ellipsoidRoundingTrack A 0 y = y := by
  simp only [ellipsoidRoundingTrack, zero_mul, Real.exp_zero, one_smul]

theorem ellipsoidRoundingTrack_ne_zero (A : E ≃L[ℝ] E) (t : ℝ) {y : E} (hy : y ≠ 0) :
    ellipsoidRoundingTrack A t y ≠ 0 :=
  smul_ne_zero (Real.exp_ne_zero _) hy

theorem ellipsoidRoundingTrack_hasDerivAt (A : E ≃L[ℝ] E) (y : E) (t : ℝ) :
    HasDerivAt (fun s => ellipsoidRoundingTrack A s y)
      (ellipsoidRoundingField A (ellipsoidRoundingTrack A t y)) t := by
  have hd := (((hasDerivAt_id t).mul_const
    (Real.log (ellipsoidRadialRatio A y))).exp).smul_const y
  simpa only [ellipsoidRoundingField, ellipsoidRoundingTrack,
    ellipsoidRadialRatio_smul A (Real.exp_pos _), one_mul, smul_smul, mul_comm, id_eq] using hd

theorem ellipsoidRoundingTrack_one_norm (A : E ≃L[ℝ] E) {y : E} (hy : y ≠ 0) :
    ‖ellipsoidRoundingTrack A 1 y‖ = ‖A.symm y‖ := by
  rw [ellipsoidRoundingTrack, one_mul, Real.exp_log (ellipsoidRadialRatio_pos A hy),
    norm_smul, Real.norm_eq_abs, abs_of_pos (ellipsoidRadialRatio_pos A hy),
    ellipsoidRadialRatio, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy)]

theorem ellipsoidRoundingTrack_contDiffOn (A : E ≃L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => ellipsoidRoundingTrack A p.1 p.2)
      (univ ×ˢ ({0}ᶜ : Set E)) := by
  have hr : ContDiffOn ℝ ∞ (fun p : ℝ × E => ellipsoidRadialRatio A p.2)
      (univ ×ˢ ({0}ᶜ : Set E)) :=
    (ellipsoidRadialRatio_contDiffOn A).comp contDiff_snd.contDiffOn (fun _ hp => hp.2)
  exact (contDiff_fst.contDiffOn.mul
    (hr.log (fun p hp => (ellipsoidRadialRatio_pos A hp.2).ne'))).exp.smul
      contDiff_snd.contDiffOn

end PoincareConjecture.M25.Topology3D
