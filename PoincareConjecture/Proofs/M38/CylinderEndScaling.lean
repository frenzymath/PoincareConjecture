import PoincareConjecture.Proofs.M38.ParameterizedBallShrinking
import PoincareConjecture.Proofs.M38.LinearSphereDiffeomorph









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38


noncomputable def endScaleProfile (c t : ℝ) : ℝ := (1 / 8) * ballShrinkProfile c (8 * t)


noncomputable def endScaleInverse (c t : ℝ) : ℝ :=
  (1 / 8) * parameterizedBallShrinkInverse c (8 * t)


theorem endScale_left_inverse {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (t : ℝ) :
    endScaleInverse c (endScaleProfile c t) = t := by
  unfold endScaleInverse endScaleProfile
  rw [show 8 * ((1 / 8 : ℝ) * ballShrinkProfile c (8 * t)) =
    ballShrinkProfile c (8 * t) by ring, parameterizedBallShrinkInverse_left hc hc1]
  ring


theorem endScale_right_inverse {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (t : ℝ) :
    endScaleProfile c (endScaleInverse c t) = t := by
  unfold endScaleInverse endScaleProfile
  rw [show 8 * ((1 / 8 : ℝ) * parameterizedBallShrinkInverse c (8 * t)) =
    parameterizedBallShrinkInverse c (8 * t) by ring, parameterizedBallShrinkInverse_right hc hc1]
  ring


theorem endScaleProfile_inner (c : ℝ) {t : ℝ} (ht : t ≤ 5 / 32) :
    endScaleProfile c t = c * t := by
  rw [endScaleProfile, ballShrinkProfile_linear c (8 * t) (by linarith)]
  ring


theorem endScaleProfile_outer (c : ℝ) {t : ℝ} (ht : 3 / 16 ≤ t) :
    endScaleProfile c t = t := by
  rw [endScaleProfile, ballShrinkProfile_outer c (8 * t) (by linarith)]
  ring


theorem endScaleProfile_strictMono {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    StrictMono (endScaleProfile c) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left
    (ballShrinkProfile_strictMono hc hc1 (mul_lt_mul_of_pos_left hst (by norm_num)))
    (by norm_num)


@[simp] theorem endScaleProfile_zero (c : ℝ) : endScaleProfile c 0 = 0 := by
  rw [endScaleProfile_inner c (by norm_num : (0 : ℝ) ≤ 5 / 32)]
  ring


@[simp] theorem endScaleProfile_one (c : ℝ) : endScaleProfile c 1 = 1 :=
  endScaleProfile_outer c (by norm_num)


theorem endScaleProfile_mem_iff {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (t : ℝ) :
    endScaleProfile c t ∈ Set.Ioo (0 : ℝ) 1 ↔ t ∈ Set.Ioo (0 : ℝ) 1 := by
  have hmono := endScaleProfile_strictMono hc hc1
  constructor
  · intro ht
    refine ⟨hmono.lt_iff_lt.mp ?_, hmono.lt_iff_lt.mp ?_⟩
    · simpa only [endScaleProfile_zero] using ht.1
    · simpa only [endScaleProfile_one] using ht.2
  · intro ht
    refine ⟨?_, ?_⟩
    · simpa only [endScaleProfile_zero] using hmono ht.1
    · simpa only [endScaleProfile_one] using hmono ht.2

variable (A : UnitTwoSphere → ℝ) (k : ℝ)


noncomputable def cylinderEndScale (p : RoundCylinderSpace) : RoundCylinderSpace :=
  (p.1, endScaleProfile (k / A p.1) p.2)


noncomputable def cylinderEndScaleInverse (p : RoundCylinderSpace) : RoundCylinderSpace :=
  (p.1, endScaleInverse (k / A p.1) p.2)

variable (hA : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ A) (hk : 0 < k)
  (hAk : ∀ z : UnitTwoSphere, k < A z)

include hk hAk in

theorem cylinderEndScale_coefficient (z : UnitTwoSphere) : 0 < k / A z ∧ k / A z < 1 :=
  ⟨div_pos hk (hk.trans (hAk z)), (div_lt_one (hk.trans (hAk z))).mpr (hAk z)⟩

include hA hk hAk


theorem cylinderEndScale_smooth :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (cylinderEndScale A k) := by
  have hc : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : RoundCylinderSpace => k / A p.1) := by
    intro p
    exact (contDiffAt_const.div contDiffAt_id (hk.trans (hAk p.1)).ne').contMDiffAt.comp
      p (hA.comp contMDiff_fst).contMDiffAt
  have hp := hc.prodMk_space
    ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd :
      ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : RoundCylinderSpace => 8 * p.2))
  exact contMDiff_fst.prodMk
    ((contDiff_const.mul contDiff_id).contMDiff.comp
      (ballShrinkProfile_joint_smooth.contMDiff.comp hp))


theorem cylinderEndScaleInverse_smooth :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (cylinderEndScaleInverse A k) := by
  have hc : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : RoundCylinderSpace => k / A p.1) := by
    intro p
    exact (contDiffAt_const.div contDiffAt_id (hk.trans (hAk p.1)).ne').contMDiffAt.comp
      p (hA.comp contMDiff_fst).contMDiffAt
  have hp := hc.prodMk_space
    ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd :
      ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : RoundCylinderSpace => 8 * p.2))
  have hi := parameterizedBallShrinkInverse_smooth.contMDiffOn.comp_contMDiff hp
    (fun p => ⟨cylinderEndScale_coefficient A k hk hAk p.1, Set.mem_univ _⟩)
  exact contMDiff_fst.prodMk ((contDiff_const.mul contDiff_id).contMDiff.comp hi)


noncomputable def cylinderEndScaleDiffeomorph :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun := cylinderEndScale A k
  invFun := cylinderEndScaleInverse A k
  left_inv p := Prod.ext rfl (endScale_left_inverse
    (cylinderEndScale_coefficient A k hk hAk p.1).1
    (cylinderEndScale_coefficient A k hk hAk p.1).2 p.2)
  right_inv p := Prod.ext rfl (endScale_right_inverse
    (cylinderEndScale_coefficient A k hk hAk p.1).1
    (cylinderEndScale_coefficient A k hk hAk p.1).2 p.2)
  contMDiff_toFun := cylinderEndScale_smooth A k hA hk hAk
  contMDiff_invFun := cylinderEndScaleInverse_smooth A k hA hk hAk

end PoincareConjecture.M38
