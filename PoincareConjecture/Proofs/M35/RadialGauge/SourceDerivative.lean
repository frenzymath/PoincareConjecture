import PoincareConjecture.Proofs.M35.RadialGauge.SourceSmoothness
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "D" => V →L[ℝ] ℝ

noncomputable def dualSquaredDifferential (p : D) : D →L[ℝ] ℝ :=
  (2 : ℝ) • (innerSL ℝ ((InnerProductSpace.toDual ℝ V).symm p)).comp
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem hasFDerivAt_dual_norm_sq (p : D) :
    HasFDerivAt (fun q : D => ‖q‖ ^ 2) (dualSquaredDifferential p) p := by
  have h := ((InnerProductSpace.toDual ℝ V).symm.hasFDerivAt (x := p)).norm_sq
  simpa only [LinearIsometryEquiv.norm_map, dualSquaredDifferential, two_smul] using h

theorem dualSquaredDifferential_norm_le (p : D) :
    ‖dualSquaredDifferential p‖ ≤ 2 * ‖p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  change ‖(2 : ℝ) * inner ℝ ((InnerProductSpace.toDual ℝ V).symm p)
    ((InnerProductSpace.toDual ℝ V).symm q)‖ ≤ _
  rw [norm_mul, Real.norm_ofNat]
  have h := norm_inner_le_norm (𝕜 := ℝ) ((InnerProductSpace.toDual ℝ V).symm p)
    ((InnerProductSpace.toDual ℝ V).symm q)
  simp only [LinearIsometryEquiv.norm_map] at h
  nlinarith

theorem dualSquaredDifferential_sub (p q : D) :
    dualSquaredDifferential p - dualSquaredDifferential q =
      dualSquaredDifferential (p - q) := by
  ext v
  simp [dualSquaredDifferential, mul_sub]

theorem graph_derivative_norm_le (q : (V × ℝ) →L[ℝ] ℝ) (p : D) :
    ‖q.comp ((ContinuousLinearMap.id ℝ V).prod p)‖ ≤
      ‖q.comp (ContinuousLinearMap.inl ℝ V ℝ)‖ + |q (0, 1)| * ‖p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have heq : q (v, p v) = q (v, 0) + (p v) * q (0, 1) := by
    have hp : (v, p v) = (v, 0) + (p v) • (0, (1 : ℝ)) := by
      ext <;> simp
    rw [hp, map_add, map_smul]
    rfl
  change ‖q (v, p v)‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖q (v, 0)‖ + ‖(p v) * q (0, 1)‖ := norm_add_le _ _
    _ ≤ ‖q.comp (ContinuousLinearMap.inl ℝ V ℝ)‖ * ‖v‖ +
        (‖p‖ * ‖v‖) * |q (0, 1)| := by
      apply add_le_add
      · exact (q.comp (ContinuousLinearMap.inl ℝ V ℝ)).le_opNorm v
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (p.le_opNorm v) (abs_nonneg _)
    _ = _ := by ring

theorem gaugeSource_fderiv_eq
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ} {x : V}
    (hb : DifferentiableAt ℝ b x) (hu : DifferentiableAt ℝ u x)
    (hdu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hG : DifferentiableAt ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x)) :
    let p := fderiv ℝ u x
    let H := fderiv ℝ (fderiv ℝ u) x
    let q := fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x)
    fderiv ℝ (gaugeSource b G u) x =
      (p.comp (fderiv ℝ b x) + H.flip (b x)) +
      (dualSquaredDifferential p).comp H +
      q.comp ((ContinuousLinearMap.id ℝ V).prod p) := by
  exact (((hdu.hasFDerivAt.clm_apply hb.hasFDerivAt).add
    ((hasFDerivAt_dual_norm_sq (fderiv ℝ u x)).comp x hdu.hasFDerivAt)).add
    (hG.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hu.hasFDerivAt))).fderiv

theorem gaugeSource_fderiv_norm_le
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ} {x : V}
    (hb : DifferentiableAt ℝ b x) (hu : DifferentiableAt ℝ u x)
    (hdu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hG : DifferentiableAt ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x)) :
    ‖fderiv ℝ (gaugeSource b G u) x‖ ≤
      (‖b x‖ + 2 * ‖fderiv ℝ u x‖) * ‖fderiv ℝ (fderiv ℝ u) x‖ +
      ‖fderiv ℝ u x‖ * ‖fderiv ℝ b x‖ +
      ‖(fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x)).comp
        (ContinuousLinearMap.inl ℝ V ℝ)‖ +
      |fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x) (0, 1)| *
        ‖fderiv ℝ u x‖ := by
  let p := fderiv ℝ u x
  let H := fderiv ℝ (fderiv ℝ u) x
  let q := fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x)
  have heq : fderiv ℝ (gaugeSource b G u) x =
      (p.comp (fderiv ℝ b x) + H.flip (b x)) +
      (dualSquaredDifferential p).comp H +
      q.comp ((ContinuousLinearMap.id ℝ V).prod p) := gaugeSource_fderiv_eq hb hu hdu hG
  rw [heq]
  have hfirst := p.opNorm_comp_le (fderiv ℝ b x)
  have hsecond : ‖H.flip (b x)‖ ≤ ‖H‖ * ‖b x‖ := by
    simpa only [ContinuousLinearMap.opNorm_flip] using H.flip.le_opNorm (b x)
  have hthird := ((dualSquaredDifferential p).opNorm_comp_le H).trans
    (mul_le_mul_of_nonneg_right (dualSquaredDifferential_norm_le p) (norm_nonneg H))
  have hfourth := graph_derivative_norm_le q p
  have hadd := (norm_add_le
    (p.comp (fderiv ℝ b x) + H.flip (b x) + (dualSquaredDifferential p).comp H)
    (q.comp ((ContinuousLinearMap.id ℝ V).prod p))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  have hadd' := norm_add_le (p.comp (fderiv ℝ b x)) (H.flip (b x))
  change _ ≤ (‖b x‖ + 2 * ‖p‖) * ‖H‖ + ‖p‖ * ‖fderiv ℝ b x‖ +
    ‖q.comp (ContinuousLinearMap.inl ℝ V ℝ)‖ + |q (0, 1)| * ‖p‖
  nlinarith

theorem gaugeSource_weighted_fderiv_bound
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ} {x : V}
    {eta B B1 L C1 H : ℝ} (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hB1 : 0 ≤ B1) (hL : 0 ≤ L)
    (hb : DifferentiableAt ℝ b x) (hu : DifferentiableAt ℝ u x)
    (hdu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hG : DifferentiableAt ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x))
    (hbb : ‖b x‖ ≤ B) (hdb : ‖fderiv ℝ b x‖ ≤ B1)
    (hub : (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ eta)
    (hHb : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H)
    (hGx : (1 + ‖x‖) *
      ‖(fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x)).comp
        (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ C1)
    (hGs : |fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x) (0, 1)| ≤ L) :
    (1 + ‖x‖) * ‖fderiv ℝ (gaugeSource b G u) x‖ ≤
      (B + 2 * eta) * H + (B1 + L) * eta + C1 := by
  have hp : ‖fderiv ℝ u x‖ ≤ eta := by
    nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg (fderiv ℝ u x))]
  have hmain := mul_le_mul_of_nonneg_left (gaugeSource_fderiv_norm_le hb hu hdu hG)
    (show 0 ≤ 1 + ‖x‖ by positivity)
  have h1 := mul_le_mul_of_nonneg_left hHb (show 0 ≤ B + 2 * eta by positivity)
  have h1a := mul_le_mul_of_nonneg_right (add_le_add hbb
    (mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num)))
      (mul_nonneg (show 0 ≤ 1 + ‖x‖ by positivity)
        (norm_nonneg (fderiv ℝ (fderiv ℝ u) x)))
  have h2 := mul_le_mul_of_nonneg_left hub hB1
  have h2a := mul_le_mul_of_nonneg_left hdb
    (mul_nonneg (show 0 ≤ 1 + ‖x‖ by positivity) (norm_nonneg (fderiv ℝ u x)))
  have h3 := mul_le_mul_of_nonneg_left hub hL
  have h3a := mul_le_mul_of_nonneg_right hGs
    (mul_nonneg (show 0 ≤ 1 + ‖x‖ by positivity) (norm_nonneg (fderiv ℝ u x)))
  nlinarith

end PoincareConjecture.M35.RadialGauge
