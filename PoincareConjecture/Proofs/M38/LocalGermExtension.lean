import PoincareConjecture.Proofs.M38.LocalPointMotion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped Manifold ContDiff NNReal

namespace PoincareConjecture.M38

noncomputable def coordinateGermCutoff (h x : StandardCapSpace) : StandardCapSpace :=
  coordinateMotionBump x • h

theorem coordinateGermCutoff_zero (h x : StandardCapSpace) (hx : 1 ≤ ‖x‖) :
    coordinateGermCutoff h x = 0 := by
  simp only [coordinateGermCutoff, coordinateMotionBump_zero x hx, zero_smul]

theorem coordinateGermError_norm (h : StandardCapSpace → StandardCapSpace) {a : ℝ≥0}
    (hh : LipschitzOnWith a h (Metric.closedBall 0 1)) (hzero : h 0 = 0)
    (x : StandardCapSpace) (hx : ‖x‖ ≤ 1) : ‖h x‖ ≤ a := by
  have hx' : x ∈ Metric.closedBall 0 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have h0 : (0 : StandardCapSpace) ∈ Metric.closedBall 0 1 := by simp
  have hb := hh.dist_le_mul x hx' 0 h0
  rw [hzero, dist_zero_right, dist_zero_right] at hb
  calc
    ‖h x‖ ≤ (a : ℝ) * ‖x‖ := hb
    _ ≤ (a : ℝ) * 1 := mul_le_mul_of_nonneg_left hx a.property
    _ = a := mul_one _

theorem coordinateGermCutoff_dist_inner (h : StandardCapSpace → StandardCapSpace)
    {a : ℝ≥0} (hh : LipschitzOnWith a h (Metric.closedBall 0 1)) (hzero : h 0 = 0)
    (x y : StandardCapSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    dist (coordinateGermCutoff (h x) x) (coordinateGermCutoff (h y) y) ≤
      (a * (coordinateMotionBumpConstant + 1) : ℝ≥0) * dist x y := by
  have hx' : x ∈ Metric.closedBall 0 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hy' : y ∈ Metric.closedBall 0 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hhxy := hh.dist_le_mul x hx' y hy'
  have hbxy := coordinateMotionBump_lipschitz.dist_le_mul x y
  simp only [dist_eq_norm, Real.norm_eq_abs] at hhxy hbxy
  have hby : |coordinateMotionBump y| ≤ 1 := by
    rw [abs_of_nonneg coordinateMotionBump.nonneg]
    exact coordinateMotionBump.le_one
  have hdecomp : coordinateGermCutoff (h x) x - coordinateGermCutoff (h y) y =
      (coordinateMotionBump x - coordinateMotionBump y) • h x +
        coordinateMotionBump y • (h x - h y) := by
    simp only [coordinateGermCutoff, sub_smul, smul_sub]
    abel
  calc
    dist (coordinateGermCutoff (h x) x) (coordinateGermCutoff (h y) y) =
        ‖(coordinateMotionBump x - coordinateMotionBump y) • h x +
          coordinateMotionBump y • (h x - h y)‖ := by rw [dist_eq_norm, hdecomp]
    _ ≤ |coordinateMotionBump x - coordinateMotionBump y| * ‖h x‖ +
        |coordinateMotionBump y| * ‖h x - h y‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        ((coordinateMotionBump x - coordinateMotionBump y) • h x)
        (coordinateMotionBump y • (h x - h y))
    _ ≤ ((coordinateMotionBumpConstant : ℝ) * ‖x - y‖) * a +
        1 * ((a : ℝ) * ‖x - y‖) := by
      exact add_le_add
        (mul_le_mul hbxy (coordinateGermError_norm h hh hzero x hx)
          (norm_nonneg _) (by positivity))
        (mul_le_mul hby hhxy (norm_nonneg _) (by positivity))
    _ = (a * (coordinateMotionBumpConstant + 1) : ℝ≥0) * dist x y := by
      simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, dist_eq_norm]
      ring

theorem coordinateGermCutoff_dist_outer (h : StandardCapSpace → StandardCapSpace)
    {a : ℝ≥0} (hh : LipschitzOnWith a h (Metric.closedBall 0 1)) (hzero : h 0 = 0)
    (x y : StandardCapSpace) (hx : ‖x‖ ≤ 1) (hy : 1 ≤ ‖y‖) :
    dist (coordinateGermCutoff (h x) x) (coordinateGermCutoff (h y) y) ≤
      (a * (coordinateMotionBumpConstant + 1) : ℝ≥0) * dist x y := by
  have hby := coordinateMotionBump_zero y hy
  have hbxy := coordinateMotionBump_lipschitz.dist_le_mul x y
  rw [hby, dist_zero_right, Real.norm_eq_abs] at hbxy
  calc
    dist (coordinateGermCutoff (h x) x) (coordinateGermCutoff (h y) y) =
        |coordinateMotionBump x| * ‖h x‖ := by
      rw [coordinateGermCutoff_zero (h y) y hy, dist_zero_right]
      exact norm_smul _ _
    _ ≤ ((coordinateMotionBumpConstant : ℝ) * dist x y) * a :=
      mul_le_mul hbxy (coordinateGermError_norm h hh hzero x hx)
        (norm_nonneg _) (by positivity)
    _ ≤ (a * (coordinateMotionBumpConstant + 1) : ℝ≥0) * dist x y := by
      simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one]
      calc
        ((coordinateMotionBumpConstant : ℝ) * dist x y) * a =
            ((a : ℝ) * coordinateMotionBumpConstant) * dist x y := by ring
        _ ≤ ((a : ℝ) * (coordinateMotionBumpConstant + 1)) * dist x y :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num)) a.property)
            dist_nonneg

theorem coordinateGermCutoff_lipschitz (h : StandardCapSpace → StandardCapSpace)
    {a : ℝ≥0} (hh : LipschitzOnWith a h (Metric.closedBall 0 1)) (hzero : h 0 = 0) :
    LipschitzWith (a * (coordinateMotionBumpConstant + 1))
      (fun x => coordinateGermCutoff (h x) x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : ‖x‖ ≤ 1
  · by_cases hy : ‖y‖ ≤ 1
    · exact coordinateGermCutoff_dist_inner h hh hzero x y hx hy
    · exact coordinateGermCutoff_dist_outer h hh hzero x y hx (le_of_not_ge hy)
  · by_cases hy : ‖y‖ ≤ 1
    · simpa only [dist_comm] using
        coordinateGermCutoff_dist_outer h hh hzero y x hy (le_of_not_ge hx)
    · rw [coordinateGermCutoff_zero (h x) x (le_of_not_ge hx),
        coordinateGermCutoff_zero (h y) y (le_of_not_ge hy), dist_self]
      positivity

theorem coordinateGermCutoff_smooth (h : StandardCapSpace → StandardCapSpace)
    (hh : ContDiffOn ℝ ∞ h (Metric.ball 0 2)) :
    ContDiff ℝ ∞ (fun x => coordinateGermCutoff (h x) x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ‖x‖ < 2
  · have hx' : x ∈ Metric.ball 0 2 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact coordinateMotionBump_smooth.contDiffAt.smul
      (hh.contDiffAt (Metric.isOpen_ball.mem_nhds hx'))
  · have hx' : 1 < ‖x‖ := by linarith
    have hnear : ∀ᶠ y : StandardCapSpace in 𝓝 x, 1 < ‖y‖ :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hx'
    exact (contDiffAt_const (c := (0 : StandardCapSpace))).congr_of_eventuallyEq
      (hnear.mono fun y hy => coordinateGermCutoff_zero (h y) y hy.le)

noncomputable def coordinateGermNormalize (h : StandardCapSpace → StandardCapSpace)
    (δ : ℝ) (x : StandardCapSpace) : StandardCapSpace :=
  δ⁻¹ • h (δ • x)

theorem coordinateGermNormalize_zero (h : StandardCapSpace → StandardCapSpace)
    (δ : ℝ) (hzero : h 0 = 0) : coordinateGermNormalize h δ 0 = 0 := by
  simp only [coordinateGermNormalize, smul_zero, hzero]

theorem coordinateGermNormalize_smooth (h : StandardCapSpace → StandardCapSpace)
    (δ : ℝ) {U : Set StandardCapSpace} (hh : ContDiffOn ℝ ∞ h U)
    (hU : ∀ x : StandardCapSpace, ‖x‖ < 2 → δ • x ∈ U) :
    ContDiffOn ℝ ∞ (coordinateGermNormalize h δ) (Metric.ball 0 2) := by
  apply ContDiffOn.const_smul
  exact hh.comp (contDiff_id.const_smul δ).contDiffOn (fun x hx => hU x (by
    simpa only [Metric.mem_ball, dist_zero_right] using hx))

theorem coordinateGermNormalize_lipschitz (h : StandardCapSpace → StandardCapSpace)
    (δ : ℝ) (hδ : 0 < δ) {a : ℝ≥0} {V : Set StandardCapSpace}
    (hh : LipschitzOnWith a h V)
    (hV : ∀ x : StandardCapSpace, ‖x‖ < 2 → δ • x ∈ V) :
    LipschitzOnWith a (coordinateGermNormalize h δ) (Metric.closedBall 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx' : ‖x‖ < 2 := by
    simp only [Metric.mem_closedBall, dist_zero_right] at hx
    linarith
  have hy' : ‖y‖ < 2 := by
    simp only [Metric.mem_closedBall, dist_zero_right] at hy
    linarith
  have hb := hh.dist_le_mul (δ • x) (hV x hx') (δ • y) (hV y hy')
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ] at hb
  calc
    dist (coordinateGermNormalize h δ x) (coordinateGermNormalize h δ y) =
        δ⁻¹ * ‖h (δ • x) - h (δ • y)‖ := by
      simp only [coordinateGermNormalize, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
    _ ≤ δ⁻¹ * ((a : ℝ) * (δ * ‖x - y‖)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hδ.le)
    _ = a * dist x y := by
      rw [dist_eq_norm]
      field_simp [hδ.ne']

theorem coordinateGerm_rescale_lipschitz (h : StandardCapSpace → StandardCapSpace)
    (δ : ℝ) (hδ : 0 < δ) {a : ℝ≥0} (hh : LipschitzWith a h) :
    LipschitzWith a (fun x => δ • h (δ⁻¹ • x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb := hh.dist_le_mul (δ⁻¹ • x) (δ⁻¹ • y)
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hδ)] at hb
  calc
    dist (δ • h (δ⁻¹ • x)) (δ • h (δ⁻¹ • y)) =
        δ * ‖h (δ⁻¹ • x) - h (δ⁻¹ • y)‖ := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    _ ≤ δ * ((a : ℝ) * (δ⁻¹ * ‖x - y‖)) :=
      mul_le_mul_of_nonneg_left hb hδ.le
    _ = a * dist x y := by
      rw [dist_eq_norm]
      field_simp [hδ.ne']

theorem coordinateGerm_rescale_formula (h : StandardCapSpace → StandardCapSpace)
    (δ : ℝ) (hδ : 0 < δ) (x : StandardCapSpace) :
    δ • coordinateGermCutoff (coordinateGermNormalize h δ (δ⁻¹ • x)) (δ⁻¹ • x) =
      coordinateMotionBump (δ⁻¹ • x) • h x := by
  simp only [coordinateGermCutoff, coordinateGermNormalize, smul_smul,
    mul_inv_cancel₀ hδ.ne', one_smul]
  congr 1
  field_simp [hδ.ne']

theorem exists_coordinateGermExtension (f : StandardCapSpace → StandardCapSpace)
    {U : Set StandardCapSpace} (hU : IsOpen U) (h0U : (0 : StandardCapSpace) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0)
    (hf' : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ StandardCapSpace)
    (R : ℝ) (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      ∃ e : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞,
        (∀ x, e x = x + coordinateMotionBump (δ⁻¹ • x) • (f x - x)) ∧
        (∀ x, ‖x‖ ≤ δ / 2 → e x = f x) ∧
        (∀ x, δ ≤ ‖x‖ → e x = x) := by
  let h : StandardCapSpace → StandardCapSpace := fun x => f x - x
  have hzero : h 0 = 0 := by simp only [h, hf0, sub_zero]
  have hsmooth : ContDiffOn ℝ ∞ h U := hf.sub contDiff_id.contDiffOn
  have hstrict : HasStrictFDerivAt h (0 : StandardCapSpace →L[ℝ] StandardCapSpace) 0 := by
    have hs := (hf.contDiffAt (hU.mem_nhds h0U)).hasStrictFDerivAt (by simp)
    rw [hf'] at hs
    simpa only [h, id_eq, sub_self] using
      hs.fun_sub (hasStrictFDerivAt_id (𝕜 := ℝ) 0)
  let a : ℝ≥0 := 1 / (2 * (coordinateMotionBumpConstant + 1))
  have ha : 0 < a := by dsimp only [a]; positivity
  have hsmall : a * (coordinateMotionBumpConstant + 1) < 1 := by
    dsimp only [a]
    have hK : coordinateMotionBumpConstant + 1 ≠ 0 := by positivity
    have heq : (1 : ℝ≥0) / (2 * (coordinateMotionBumpConstant + 1)) *
        (coordinateMotionBumpConstant + 1) = 1 / 2 := by field_simp [hK]
    rw [heq]
    norm_num
  obtain ⟨V, hV, hLip⟩ := hstrict.exists_lipschitzOnWith_of_nnnorm_lt a (by simpa using ha)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds h0U) hV)
  let δ : ℝ := min (r / 4) (R / 2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδR : δ < R := (min_le_right _ _).trans_lt (by linarith)
  have hδr : δ ≤ r / 4 := min_le_left _ _
  have hscaled : ∀ x : StandardCapSpace, ‖x‖ < 2 → δ • x ∈ U ∩ V := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    exact (mul_lt_mul_of_pos_left hx hδ).trans (by linarith)
  let H : StandardCapSpace → StandardCapSpace := coordinateGermNormalize h δ
  have hH0 : H 0 = 0 := coordinateGermNormalize_zero h δ hzero
  have hHs : ContDiffOn ℝ ∞ H (Metric.ball 0 2) :=
    coordinateGermNormalize_smooth h δ hsmooth (fun x hx => (hscaled x hx).1)
  have hHl : LipschitzOnWith a H (Metric.closedBall 0 1) :=
    coordinateGermNormalize_lipschitz h δ hδ hLip (fun x hx => (hscaled x hx).2)
  let Q : StandardCapSpace → StandardCapSpace := fun x => coordinateGermCutoff (H x) x
  have hQs : ContDiff ℝ ∞ Q := coordinateGermCutoff_smooth H hHs
  have hQl : LipschitzWith (a * (coordinateMotionBumpConstant + 1)) Q :=
    coordinateGermCutoff_lipschitz H hHl hH0
  let g : StandardCapSpace → StandardCapSpace := fun x => δ • Q (δ⁻¹ • x)
  have hgs : ContDiff ℝ ∞ g := (hQs.comp (contDiff_id.const_smul δ⁻¹)).const_smul δ
  have hgl : LipschitzWith (a * (coordinateMotionBumpConstant + 1)) g :=
    coordinateGerm_rescale_lipschitz Q δ hδ hQl
  let e := smallCoordinateDiffeomorph g hgl hsmall hgs
  have he : ∀ x, e x = x + coordinateMotionBump (δ⁻¹ • x) • (f x - x) := by
    intro x
    rw [smallCoordinateDiffeomorph_apply]
    exact congrArg (fun y => x + y) (coordinateGerm_rescale_formula h δ hδ x)
  refine ⟨δ, hδ, hδR, e, he, ?_, ?_⟩
  · intro x hx
    have hinner : ‖δ⁻¹ • x‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
      calc
        δ⁻¹ * ‖x‖ ≤ δ⁻¹ * (δ / 2) := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hδ.le)
        _ = 1 / 2 := by field_simp [hδ.ne']
    rw [he, coordinateMotionBump_one _ hinner, one_smul]
    abel
  · intro x hx
    have houter : 1 ≤ ‖δ⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
      calc
        1 = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
        _ ≤ δ⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hδ.le)
    rw [he, coordinateMotionBump_zero _ houter, zero_smul, add_zero]

end PoincareConjecture.M38
