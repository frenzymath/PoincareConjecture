import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Triangle
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.AngularCoordinate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

noncomputable def equilateralVertex (j : ℤ) : ℂ :=
  Circle.exp ((2 * Real.pi / 3) * j)

private theorem equilateralVertex_add (i j : ℤ) :
    equilateralVertex (i + j) = equilateralVertex i * equilateralVertex j := by
  simp only [equilateralVertex, Int.cast_add, mul_add, Circle.exp_add, Circle.coe_mul]

theorem equilateralVertex_one :
    equilateralVertex 1 = (-1 / 2 : ℝ) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  simp only [equilateralVertex, Int.cast_one, mul_one, Circle.coe_exp]
  rw [Complex.exp_ofReal_mul_I, hcos, hsin]

theorem equilateralVertex_neg_one :
    equilateralVertex (-1) = (-1 / 2 : ℝ) - (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  simp only [equilateralVertex, Int.cast_neg, Int.cast_one, mul_neg, mul_one, Circle.coe_exp]
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, hcos, hsin]
  push_cast
  ring

noncomputable def equilateralCorner (ρ : ℝ → ℝ) (s : ℝ) : ℂ :=
  ((1 - 3 * ρ s / 2 : ℝ) : ℂ) + ((Real.sqrt 3 * s / 2 : ℝ) : ℂ) * Complex.I

theorem roundedCorner_equilateral_eq (ρ : ℝ → ℝ) (j : ℤ) (s : ℝ) :
    roundedCorner ρ (equilateralVertex j)
    (equilateralVertex j - equilateralVertex (j - 1))
    (equilateralVertex (j + 1) - equilateralVertex j) s =
      equilateralVertex j * equilateralCorner ρ s := by
  rw [show j - 1 = j + (-1) by omega, equilateralVertex_add, equilateralVertex_add,
    equilateralVertex_one, equilateralVertex_neg_one]
  simp only [roundedCorner, equilateralCorner, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_one]
  ring

theorem roundedVertexPath_equilateral_eq (ρ : ℝ → ℝ) (t : ℝ) :
    roundedVertexPath ρ equilateralVertex t =
      equilateralVertex ⌊t + 1 / 2⌋ * equilateralCorner ρ (t - ⌊t + 1 / 2⌋) :=
  roundedCorner_equilateral_eq ρ _ _

theorem smoothAbsolute_le_half_on_corner {ρ : ℝ → ℝ} {δ s : ℝ}
    (hδ : δ < 1 / 4) (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ) (hs : |s| ≤ 1 / 2) :
    ρ s ≤ 1 / 2 := by
  by_cases h : δ ≤ |s|
  · rwa [htail s h]
  · have h' : |s| < δ := lt_of_not_ge h
    linarith [(hbound s).2]

theorem equilateralCorner_re_pos {ρ : ℝ → ℝ} {δ s : ℝ}
    (hδ : δ < 1 / 4) (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ) (hs : |s| ≤ 1 / 2) :
    0 < (equilateralCorner ρ s).re := by
  have hρ := smoothAbsolute_le_half_on_corner hδ htail hbound hs
  simp only [equilateralCorner, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linarith

theorem equilateralCorner_rotating_re_pos {ρ : ℝ → ℝ} {δ s : ℝ}
    (hδ : δ < 1 / 4) (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ) (hs : |s| ≤ 1 / 2) :
    0 < (equilateralCorner ρ s * (Circle.exp (-(2 * Real.pi / 3 * s)) : ℂ)).re := by
  have hreal := equilateralCorner_re_pos hδ htail hbound hs
  have hπ := Real.pi_pos
  have hs' := abs_le.mp hs
  have hangle : 2 * Real.pi / 3 * s ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith
  have hcos := Real.cos_pos_of_mem_Ioo hangle
  have hsin : 0 ≤ s * Real.sin (2 * Real.pi / 3 * s) := by
    by_cases h : 0 ≤ s
    · exact mul_nonneg h (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by
        nlinarith [hangle.2]))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge h)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge h)) (by
            nlinarith [hangle.1]))
  have him : 0 ≤ (equilateralCorner ρ s).im * Real.sin (2 * Real.pi / 3 * s) := by
    simp only [equilateralCorner, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) hsin]
  simpa only [Complex.mul_re, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg, mul_neg, sub_neg_eq_add]
    using add_pos_of_pos_of_nonneg (mul_pos hreal hcos) him

theorem roundedEquilateral_rotating_re_pos {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : δ < 1 / 4) (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ) (t : ℝ) :
    0 < (roundedVertexPath ρ equilateralVertex t *
      (Circle.exp (-(2 * Real.pi / 3 * t)) : ℂ)).re := by
  let j : ℤ := ⌊t + 1 / 2⌋
  have hjlo : (j : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hjhi : t + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hs : |t - (j : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hphase : equilateralVertex j * (Circle.exp (-(2 * Real.pi / 3 * t)) : ℂ) =
      (Circle.exp (-(2 * Real.pi / 3 * (t - j))) : ℂ) := by
    rw [equilateralVertex, ← Circle.coe_mul, ← Circle.exp_add]
    congr 2
    ring
  rw [roundedVertexPath_equilateral_eq]
  change 0 < (equilateralVertex j * equilateralCorner ρ (t - j) * _).re
  rw [mul_right_comm, hphase, mul_comm]
  exact equilateralCorner_rotating_re_pos hδ htail hbound hs

theorem periodic_roundedEquilateral (ρ : ℝ → ℝ) :
    Periodic (roundedVertexPath ρ equilateralVertex) 3 := by
  apply periodic_roundedVertexPath ρ equilateralVertex (3 : ℤ)
  intro j
  have he : (2 * Real.pi / 3) * ((j + 3 : ℤ) : ℝ) =
      (2 * Real.pi / 3) * j + 2 * Real.pi := by push_cast; ring
  simp only [equilateralVertex, he]
  exact congrArg Subtype.val (Circle.periodic_exp _)

theorem periodic_equilateralVertex : Periodic equilateralVertex 3 := by
  intro j
  have he : (2 * Real.pi / 3) * ((j + 3 : ℤ) : ℝ) =
      (2 * Real.pi / 3) * j + 2 * Real.pi := by push_cast; ring
  simp only [equilateralVertex, he]
  exact congrArg Subtype.val (Circle.periodic_exp _)

noncomputable def roundedEquilateralAngle (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  circleAngularCoordinate (LinearIsometryEquiv.refl ℝ ℂ)
    (2 * Real.pi / 3 * t, roundedVertexPath ρ equilateralVertex t)

theorem contDiff_roundedEquilateral {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ)
    (hρ : ContDiff ℝ ∞ ρ) : ContDiff ℝ ∞ (roundedVertexPath ρ equilateralVertex) := by
  have h := contDiff_roundedVertexPath (P := fun _ : ℝ => equilateralVertex)
    hδ (by linarith) htail hbound hρ (fun _ => contDiff_const)
  have hm : ContDiff ℝ ∞ (fun t : ℝ => ((0 : ℝ), t)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using h.comp hm

theorem contDiff_roundedEquilateralAngle {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ)
    (hρ : ContDiff ℝ ∞ ρ) : ContDiff ℝ ∞ (roundedEquilateralAngle ρ) := by
  have hγ := contDiff_roundedEquilateral hδ hδsmall htail hbound hρ
  rw [contDiff_iff_contDiffAt]
  intro t
  have hmem : (2 * Real.pi / 3 * t, roundedVertexPath ρ equilateralVertex t) ∈
      {p : ℝ × ℂ | (LinearIsometryEquiv.refl ℝ ℂ).symm p.2 *
        (Circle.exp (-p.1) : ℂ) ∈ Complex.slitPlane} := by
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (roundedEquilateral_rotating_re_pos
      hδsmall htail hbound t))
  exact ((contDiffOn_circleAngularCoordinate (LinearIsometryEquiv.refl ℝ ℂ)).contDiffAt
    ((isOpen_circleAngularCoordinate_domain _).mem_nhds hmem)).comp t
      ((contDiff_const.mul contDiff_id).prodMk hγ).contDiffAt

theorem roundedEquilateralAngle_add_three (ρ : ℝ → ℝ) (t : ℝ) :
    roundedEquilateralAngle ρ (t + 3) = roundedEquilateralAngle ρ t + 2 * Real.pi := by
  have hphase : (Circle.exp (-(2 * Real.pi / 3 * (t + 3))) : ℂ) =
      (Circle.exp (-(2 * Real.pi / 3 * t)) : ℂ) := by
    rw [show -(2 * Real.pi / 3 * (t + 3)) = -(2 * Real.pi / 3 * t) - 2 * Real.pi by ring]
    exact congrArg Subtype.val (Circle.periodic_exp.sub_eq _)
  simp only [roundedEquilateralAngle, circleAngularCoordinate,
    periodic_roundedEquilateral ρ t, hphase]
  ring

theorem norm_roundedEquilateral_mem_Icc {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : δ < 1 / 4) (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ) (t : ℝ) :
    ‖roundedVertexPath ρ equilateralVertex t‖ ∈ Icc (1 / 4 : ℝ) 1 := by
  let j : ℤ := ⌊t + 1 / 2⌋
  let s : ℝ := t - j
  have hjlo : (j : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hjhi : t + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hs : |s| ≤ 1 / 2 := abs_le.mpr ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩
  rw [roundedVertexPath_equilateral_eq, norm_mul]
  change ‖equilateralVertex j‖ * ‖equilateralCorner ρ s‖ ∈ _
  rw [show ‖equilateralVertex j‖ = 1 from Circle.norm_coe _, one_mul]
  have hrho : ρ s ≤ 1 / 2 := smoothAbsolute_le_half_on_corner hδ htail hbound hs
  have hrho0 : 0 ≤ ρ s := (abs_nonneg s).trans (hbound s).1
  have hsq : s ^ 2 ≤ (ρ s) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) hrho0).mpr (hbound s).1
  have hnorm : ‖equilateralCorner ρ s‖ ^ 2 = (1 - 3 * ρ s / 2) ^ 2 + 3 * s ^ 2 / 4 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, equilateralCorner, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  constructor
  · have h := Complex.re_le_norm (equilateralCorner ρ s)
    simp only [equilateralCorner, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
    change 1 - 3 * ρ s / 2 ≤ ‖equilateralCorner ρ s‖ at h
    linarith
  · have hrhosq : (ρ s) ^ 2 ≤ ρ s := by nlinarith
    nlinarith [norm_nonneg (equilateralCorner ρ s)]

end Poincare.Manifold.Schoenflies.Plane
