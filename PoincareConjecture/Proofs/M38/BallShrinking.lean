import PoincareConjecture.Proofs.M38.BallPatchDiffeomorph
import PoincareConjecture.Proofs.M38.RadialCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

noncomputable def ballShrinkTransition (t : ℝ) : ℝ :=
  t * Real.smoothTransition (4 * t - 5)

theorem ballShrinkTransition_zero (t : ℝ) (ht : t ≤ 5 / 4) :
    ballShrinkTransition t = 0 := by
  simp [ballShrinkTransition, Real.smoothTransition.zero_of_nonpos (by linarith :
    4 * t - 5 ≤ 0)]

theorem ballShrinkTransition_outer (t : ℝ) (ht : 3 / 2 ≤ t) :
    ballShrinkTransition t = t := by
  simp [ballShrinkTransition, Real.smoothTransition.one_of_one_le (by linarith :
    1 ≤ 4 * t - 5)]

theorem ballShrinkTransition_nonneg (t : ℝ) : 0 ≤ ballShrinkTransition t := by
  by_cases ht : 0 ≤ t
  · exact mul_nonneg ht (Real.smoothTransition.nonneg _)
  · simpa only [ballShrinkTransition_zero t (by linarith)] using (le_refl (0 : ℝ))

theorem ballShrinkTransition_monotone : Monotone ballShrinkTransition := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · exact mul_le_mul hab (Real.smoothTransition.monotone (by linarith))
      (Real.smoothTransition.nonneg _) (ha.trans hab)
  · rw [ballShrinkTransition_zero a (by linarith)]
    exact ballShrinkTransition_nonneg b

theorem ballShrinkTransition_smooth : ContDiff ℝ ∞ ballShrinkTransition :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

noncomputable def ballShrinkProfile (c t : ℝ) : ℝ :=
  c * t + (1 - c) * ballShrinkTransition t

theorem ballShrinkProfile_linear (c t : ℝ) (ht : t ≤ 5 / 4) :
    ballShrinkProfile c t = c * t := by
  rw [ballShrinkProfile, ballShrinkTransition_zero t ht, mul_zero, add_zero]

@[simp] theorem ballShrinkProfile_zero (c : ℝ) : ballShrinkProfile c 0 = 0 := by
  rw [ballShrinkProfile_linear c 0 (by norm_num), mul_zero]

theorem ballShrinkProfile_outer (c t : ℝ) (ht : 3 / 2 ≤ t) :
    ballShrinkProfile c t = t := by
  rw [ballShrinkProfile, ballShrinkTransition_outer t ht]
  ring

theorem ballShrinkProfile_smooth (c : ℝ) : ContDiff ℝ ∞ (ballShrinkProfile c) :=
  (contDiff_const.mul contDiff_id).add (contDiff_const.mul ballShrinkTransition_smooth)

theorem ballShrinkProfile_strictMono {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    StrictMono (ballShrinkProfile c) := by
  intro a b hab
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hab hc)
    (mul_le_mul_of_nonneg_left (ballShrinkTransition_monotone hab.le)
      (sub_nonneg.mpr hc1.le))

theorem ballShrinkProfile_deriv_pos {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (t : ℝ) :
    0 < deriv (ballShrinkProfile c) t := by
  have hd := ((hasDerivAt_id t).const_mul c).add
    (((ballShrinkTransition_smooth.differentiable (by simp)) t).hasDerivAt.const_mul (1 - c))
  have hderiv : deriv (ballShrinkProfile c) t =
      c + (1 - c) * deriv ballShrinkTransition t := by
    convert hd.deriv using 1 <;> first | rfl | simp only [mul_one]
  rw [hderiv]
  exact add_pos_of_pos_of_nonneg hc
    (mul_nonneg (sub_nonneg.mpr hc1.le) ballShrinkTransition_monotone.deriv_nonneg)

theorem ballShrinkProfile_lower {c : ℝ} (hc1 : c < 1) (t : ℝ) :
    c * t ≤ ballShrinkProfile c t := by
  exact le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr hc1.le) (ballShrinkTransition_nonneg t))

theorem ballShrinkProfile_le_self {c : ℝ} (hc1 : c < 1) (t : ℝ) (ht : 0 ≤ t) :
    ballShrinkProfile c t ≤ t := by
  have htransition : ballShrinkTransition t ≤ t := by
    simpa only [ballShrinkTransition, mul_one] using
      mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (4 * t - 5)) ht
  have hterm := mul_le_mul_of_nonneg_left htransition (sub_nonneg.mpr hc1.le)
  dsimp only [ballShrinkProfile]
  nlinarith

theorem ballShrinkProfile_surjective {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Function.Surjective (ballShrinkProfile c) := by
  intro y
  by_cases hy : 0 ≤ y
  · have hab : y ≤ y / c := (le_div_iff₀ hc).mpr (by nlinarith)
    have hupper : y ≤ ballShrinkProfile c (y / c) := by
      calc
        y = c * (y / c) := (mul_div_cancel₀ y hc.ne').symm
        _ ≤ ballShrinkProfile c (y / c) := ballShrinkProfile_lower hc1 (y / c)
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc hab
      (ballShrinkProfile_smooth c).continuous.continuousOn
        ⟨ballShrinkProfile_le_self hc1 y hy, hupper⟩
    exact ⟨t, ht⟩
  · refine ⟨y / c, ?_⟩
    have hnonpos : y / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
    rw [ballShrinkProfile_linear c (y / c) (by linarith), mul_div_cancel₀ _ hc.ne']

noncomputable def ballShrinkOrderIso (c : ℝ) (hc : 0 < c) (hc1 : c < 1) : ℝ ≃o ℝ :=
  (ballShrinkProfile_strictMono hc hc1).orderIsoOfSurjective _
    (ballShrinkProfile_surjective hc hc1)

@[simp] theorem ballShrinkOrderIso_apply (c : ℝ) (hc : 0 < c) (hc1 : c < 1) (t : ℝ) :
    ballShrinkOrderIso c hc hc1 t = ballShrinkProfile c t := rfl

@[simp] theorem ballShrinkOrderIso_symm_zero {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (ballShrinkOrderIso c hc hc1).symm 0 = 0 := by
  apply (ballShrinkOrderIso c hc hc1).injective
  simp

theorem ballShrinkOrderIso_symm_smooth {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ContDiff ℝ ∞ (ballShrinkOrderIso c hc hc1).symm := by
  apply (ballShrinkOrderIso c hc hc1).toHomeomorph.contDiff_symm_deriv
    (fun t => (ballShrinkProfile_deriv_pos hc hc1 t).ne')
    (fun t => ((ballShrinkProfile_smooth c).differentiable (by simp) t).hasDerivAt)
    (ballShrinkProfile_smooth c)

theorem ballShrinkOrderIso_symm_linear {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (t : ℝ) (ht : t ≤ c * (5 / 4)) :
    (ballShrinkOrderIso c hc hc1).symm t = t / c := by
  apply (ballShrinkOrderIso c hc hc1).injective
  rw [OrderIso.apply_symm_apply, ballShrinkOrderIso_apply,
    ballShrinkProfile_linear c (t / c) ((div_le_iff₀ hc).mpr (by nlinarith))]
  exact (mul_div_cancel₀ t hc.ne').symm

noncomputable def ballShrinkDiffeomorph (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ where
  toFun := capRadialMap (ballShrinkOrderIso c hc hc1)
  invFun := capRadialMap (ballShrinkOrderIso c hc hc1).symm
  left_inv := capRadialMap_left_inverse _ (by simp)
  right_inv := capRadialMap_left_inverse _ (ballShrinkOrderIso_symm_zero hc hc1)
  contMDiff_toFun := contMDiff_iff_contDiff.mpr
    (capRadialMap_smooth _ (ballShrinkProfile_smooth c) (5 / 4) c (by norm_num)
      (fun t ht => ballShrinkProfile_linear c t ht))
  contMDiff_invFun := contMDiff_iff_contDiff.mpr
    (capRadialMap_smooth _ (ballShrinkOrderIso_symm_smooth hc hc1) (c * (5 / 4)) c⁻¹
      (by positivity) (fun t ht => by
        rw [ballShrinkOrderIso_symm_linear hc hc1 t ht]
        exact div_eq_inv_mul t c))

theorem ballShrinkDiffeomorph_norm {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (x : StandardCapSpace) :
    ‖ballShrinkDiffeomorph c hc hc1 x‖ = ballShrinkProfile c ‖x‖ := by
  apply capRadialMap_norm _ (by simp)
  intro t ht
  simpa using (ballShrinkProfile_strictMono hc hc1).monotone ht

theorem ballShrinkDiffeomorph_linear {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (x : StandardCapSpace) (hx : ‖x‖ ≤ 5 / 4) :
    ballShrinkDiffeomorph c hc hc1 x = c • x :=
  capRadialMap_eq_smul _ c x (ballShrinkProfile_linear c ‖x‖ hx)

theorem ballShrinkDiffeomorph_symm_linear {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (x : StandardCapSpace) (hx : ‖x‖ ≤ c * (5 / 4)) :
    (ballShrinkDiffeomorph c hc hc1).symm x = c⁻¹ • x := by
  apply capRadialMap_eq_smul _ c⁻¹ x
  rw [ballShrinkOrderIso_symm_linear hc hc1 ‖x‖ hx]
  exact div_eq_inv_mul ‖x‖ c

theorem ballShrinkDiffeomorph_outer {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (x : StandardCapSpace) (hx : 3 / 2 ≤ ‖x‖) :
    ballShrinkDiffeomorph c hc hc1 x = x := by
  change capRadialMap (ballShrinkOrderIso c hc hc1) x = x
  simpa only [one_smul] using capRadialMap_eq_smul
    (ballShrinkOrderIso c hc hc1) 1 x (by
      rw [ballShrinkOrderIso_apply, ballShrinkProfile_outer c ‖x‖ hx, one_mul])

theorem ballShrinkDiffeomorph_closedBall {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (r : ℝ) (hr : r ≤ 5 / 4) :
    ballShrinkDiffeomorph c hc hc1 '' Metric.closedBall 0 r = Metric.closedBall 0 (c * r) := by
  ext y
  obtain ⟨x, rfl⟩ := (ballShrinkDiffeomorph c hc hc1).surjective y
  have himage : ballShrinkDiffeomorph c hc hc1 x ∈
      ballShrinkDiffeomorph c hc hc1 '' Metric.closedBall 0 r ↔ x ∈ Metric.closedBall 0 r := by
    constructor
    · rintro ⟨z, hz, heq⟩
      exact (ballShrinkDiffeomorph c hc hc1).injective heq ▸ hz
    · exact Set.mem_image_of_mem _
  change ballShrinkDiffeomorph c hc hc1 x ∈
      ballShrinkDiffeomorph c hc hc1 '' Metric.closedBall 0 r ↔
    ballShrinkDiffeomorph c hc hc1 x ∈ Metric.closedBall 0 (c * r)
  rw [himage]
  simp only [Metric.mem_closedBall, dist_zero_right, ballShrinkDiffeomorph_norm]
  rw [← ballShrinkProfile_linear c r hr, (ballShrinkProfile_strictMono hc hc1).le_iff_le]

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

noncomputable def surgeryBallShrinkDiffeomorph (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞ :=
  surgeryBallPatchDiffeomorph (ballShrinkDiffeomorph c hc hc1)
    (ballShrinkDiffeomorph_outer hc hc1) B

theorem surgeryBallShrinkDiffeomorph_map {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (x : StandardCapSpace) (hx : ‖x‖ ≤ 5 / 4) :
    surgeryBallShrinkDiffeomorph B c hc hc1 (B.map x) = B.map (c • x) := by
  have hxball : x ∈ Metric.ball 0 2 := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  change surgeryBallPatchDiffeomorph (ballShrinkDiffeomorph c hc hc1)
      (ballShrinkDiffeomorph_outer hc hc1) B (B.map x) = B.map (c • x)
  rw [surgeryBallPatchDiffeomorph_map _ _ _ hxball, ballShrinkDiffeomorph_linear hc hc1 x hx]

theorem surgeryBallShrinkDiffeomorph_symm_map {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (x : StandardCapSpace) (hx : ‖x‖ ≤ c * (5 / 4)) :
    (surgeryBallShrinkDiffeomorph B c hc hc1).symm (B.map x) = B.map (c⁻¹ • x) := by
  have hxball : x ∈ Metric.ball 0 2 := by
    simp only [Metric.mem_ball, dist_zero_right]
    nlinarith
  change (surgeryBallPatchDiffeomorph (ballShrinkDiffeomorph c hc hc1)
      (ballShrinkDiffeomorph_outer hc hc1) B).symm (B.map x) = B.map (c⁻¹ • x)
  rw [surgeryBallPatchDiffeomorph_symm_map _ _ _ hxball,
    ballShrinkDiffeomorph_symm_linear hc hc1 x hx]

theorem surgeryBallShrinkDiffeomorph_closedImage {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    surgeryBallShrinkDiffeomorph B c hc hc1 '' (B.map '' Metric.closedBall 0 (5 / 4)) =
      B.map '' Metric.closedBall 0 (c * (5 / 4)) := by
  calc
    surgeryBallShrinkDiffeomorph B c hc hc1 '' (B.map '' Metric.closedBall 0 (5 / 4)) =
        B.map '' (ballShrinkDiffeomorph c hc hc1 '' Metric.closedBall 0 (5 / 4)) := by
      rw [Set.image_image, Set.image_image]
      apply Set.image_congr
      intro x hx
      exact surgeryBallPatchDiffeomorph_map _ _ B
        (Metric.closedBall_subset_ball (by norm_num : (5 / 4 : ℝ) < 2) hx)
    _ = B.map '' Metric.closedBall 0 (c * (5 / 4)) := by
      rw [ballShrinkDiffeomorph_closedBall hc hc1 (5 / 4) le_rfl]

theorem surgeryBallShrinkDiffeomorph_eq_self_off_compact {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {x : A.carrier} (hx : x ∉ B.map '' Metric.closedBall 0 (3 / 2)) :
    surgeryBallShrinkDiffeomorph B c hc hc1 x = x :=
  surgeryBallPatchDiffeomorph_eq_self_off_compact _ _ B hx

theorem surgeryBallShrinkDiffeomorph_symm_eq_self_off_compact {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {x : A.carrier} (hx : x ∉ B.map '' Metric.closedBall 0 (3 / 2)) :
    (surgeryBallShrinkDiffeomorph B c hc hc1).symm x = x :=
  surgeryBallPatchDiffeomorph_symm_eq_self_off_compact _ _ B hx

theorem exists_surgeryBallShrink (rho : ℝ) (hrho : 0 < rho) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ c * (5 / 4) < rho ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 → e (B.map x) = B.map (c • x)) ∧
      e '' (B.map '' Metric.closedBall 0 (5 / 4)) ⊆ B.map '' Metric.ball 0 rho ∧
      (∀ x : A.carrier, x ∉ B.map '' Metric.closedBall 0 (3 / 2) → e x = x) ∧
      (∀ x : A.carrier, x ∉ B.map '' Metric.closedBall 0 (3 / 2) → e.symm x = x) := by
  let c : ℝ := min (1 / 2) (rho / 4)
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc1 : c < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hcr : c ≤ rho / 4 := min_le_right _ _
  have hsmall : c * (5 / 4) < rho := by
    calc
      c * (5 / 4) ≤ (rho / 4) * (5 / 4) :=
        mul_le_mul_of_nonneg_right hcr (by norm_num)
      _ < rho := by nlinarith
  refine ⟨surgeryBallShrinkDiffeomorph B c hc hc1, c, hc, hc1, hsmall,
    surgeryBallShrinkDiffeomorph_map B hc hc1, ?_,
    (fun _ hx => surgeryBallShrinkDiffeomorph_eq_self_off_compact B hc hc1 hx),
    (fun _ hx => surgeryBallShrinkDiffeomorph_symm_eq_self_off_compact B hc hc1 hx)⟩
  rw [surgeryBallShrinkDiffeomorph_closedImage B hc hc1]
  exact Set.image_mono (Metric.closedBall_subset_ball hsmall)

end PoincareConjecture.M38
