import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnTransverse
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_boundary_return_velocity_ne
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hT : 0 < T)
    (h0 : ‖gamma 0‖ = 1) (hinside : ∀ x ∈ Ioo 0 T, 1 < ‖gamma x‖)
    (hinward : 0 < inner ℝ (gamma 0) (deriv gamma 0))
    (hreturn : gamma 0 = gamma T) : deriv gamma 0 ≠ deriv gamma T := by
  intro hvel
  have hnormT : ‖gamma T‖ = 1 := by rw [← hreturn, h0]
  have hd : HasDerivAt (fun x => ‖gamma x‖ ^ 2)
      (2 * inner ℝ (gamma T) (deriv gamma T)) T :=
    (hg.differentiable (by simp) T).hasDerivAt.norm_sq
  have hpos : 0 < 2 * inner ℝ (gamma T) (deriv gamma T) := by
    rw [← hreturn, ← hvel]
    positivity
  have hslope := hd.tendsto_slope_zero_left.eventually_const_lt hpos
  have hnear : ∀ᶠ h in 𝓝[<] (0 : ℝ), h ∈ Ioo (-T) 0 :=
    Ioo_mem_nhdsLT (by linarith : -T < 0)
  obtain ⟨h, hh, hs⟩ := (hnear.and hslope).exists
  have hnorm := hinside (T + h) ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hdiff : 0 < ‖gamma (T + h)‖ ^ 2 - ‖gamma T‖ ^ 2 := by
    rw [hnormT]
    nlinarith
  have hnegative : h⁻¹ * (‖gamma (T + h)‖ ^ 2 - ‖gamma T‖ ^ 2) < 0 :=
    mul_neg_of_neg_of_pos (inv_lt_zero'.mpr hh.2) hdiff
  change 0 < h⁻¹ * (‖gamma (T + h)‖ ^ 2 - ‖gamma T‖ ^ 2) at hs
  exact (not_lt_of_ge hs.le) hnegative

theorem m64Intrinsic_unit_boundary_return_transverse
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : G.IsGeodesicOn gamma (Icc 0 T))
    (hT : 0 < T) (h0 : ‖gamma 0‖ = 1)
    (hinside : ∀ x ∈ Ioo 0 T, 1 < ‖gamma x‖)
    (hinward : 0 < inner ℝ (gamma 0) (deriv gamma 0))
    (hunit : ∀ x ∈ Icc 0 T, G.inner (gamma x) (deriv gamma x) (deriv gamma x) = 1)
    (hreturn : gamma 0 = gamma T) :
    LinearIndependent ℝ (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates) := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hreg (x : ℝ) (hx : x ∈ Icc 0 T) : deriv gamma x ≠ 0 := by
    intro hz
    have h := hunit x hx
    simp only [hz, map_zero] at h
    norm_num at h
  have hsame := m64Intrinsic_boundary_return_velocity_ne hg hT h0 hinside hinward hreturn
  have hopp := m64Intrinsic_regular_return_velocity_ne_neg G hg hgeo hT hreg hreturn
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨neg_ne_zero.mpr (hreg T hlast), ?_⟩
  intro c hc
  have hw : G.inner (gamma 0) (deriv gamma T) (deriv gamma T) = 1 := by
    rw [hreturn]
    exact hunit T hlast
  have hsq : c ^ 2 = 1 := by
    have h := hunit 0 hzero
    rw [← hc] at h
    simp only [map_smul, smul_apply, smul_eq_mul, map_neg, neg_apply, hw] at h
    nlinarith only [h]
  have hcCases : c = 1 ∨ c = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hsq)
  rcases hcCases with rfl | rfl
  · apply hopp
    simpa only [one_smul] using hc.symm
  · apply hsame
    simpa only [neg_one_smul, neg_neg] using hc.symm

end PoincareConjecture
