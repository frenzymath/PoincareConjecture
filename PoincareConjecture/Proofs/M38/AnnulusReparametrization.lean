import PoincareConjecture.Proofs.M38.RadialCoordinates
import PoincareConjecture.Proofs.M38.SmoothChart
import PoincareConjecture.Definitions.Ch15.SurgeryTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {a : ℝ} (ha : 0 < a) (ha1 : a < 1)

theorem annulusRadial_mapsTo :
    Set.MapsTo (capRadialDiffeomorph 1 a ha ha1)
      (Metric.ball 0 2) (Metric.ball 0 2) := by
  intro x hx
  have hmem : capRadialDiffeomorph 1 a ha ha1 x ∈ Metric.ball 0 (1 + a) := by
    rw [← capRadialDiffeomorph_ball_two ha ha1]
    exact Set.mem_image_of_mem _ hx
  exact Metric.ball_subset_ball (by linarith) hmem

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

noncomputable def annulusReparametrizedBall : SurgeryBallEmbedding A := by
  let e := capRadialDiffeomorph 1 a ha ha1
  let f := B.map ∘ e
  let g := e.symm ∘ B.inverse
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 2) :=
    B.map_smooth.comp e.contMDiff.contMDiffOn (annulusRadial_mapsTo ha ha1)
  have hsub : f '' Metric.ball 0 2 ⊆ B.map '' Metric.ball 0 2 := by
    rintro _ ⟨x, hx, rfl⟩
    exact Set.mem_image_of_mem _ (annulusRadial_mapsTo ha ha1 hx)
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) :=
    e.symm.contMDiff.comp_contMDiffOn (B.inverse_smooth.mono hsub)
  have hleft : Set.LeftInvOn g f (Metric.ball 0 2) := by
    intro x hx
    change e.symm (B.inverse (B.map (e x))) = x
    rw [B.left_inverse (annulusRadial_mapsTo ha ha1 hx), e.symm_apply_apply]
  exact {
    map := f
    inverse := g
    map_smooth := hf
    inverse_smooth := hg
    left_inverse := hleft
    right_inverse := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg f (hleft hx)
    open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball hf hg hleft }

theorem annulusReparametrizedBall_map (x : StandardCapSpace) :
    (annulusReparametrizedBall ha ha1 B).map x =
      B.map (capRadialDiffeomorph 1 a ha ha1 x) := rfl

theorem annulusReparametrizedBall_inverse (x : A.carrier) :
    (annulusReparametrizedBall ha ha1 B).inverse x =
      (capRadialDiffeomorph 1 a ha ha1).symm (B.inverse x) := rfl

theorem annulusReparametrizedBall_closedBall :
    (annulusReparametrizedBall ha ha1 B).closedBall = B.closedBall := by
  change (B.map ∘ capRadialDiffeomorph 1 a ha ha1) '' Metric.closedBall 0 1 =
    B.map '' Metric.closedBall 0 1
  rw [Set.image_comp, capRadialDiffeomorph_closedBall ha ha1]

theorem annulusReparametrizedBall_image :
    (annulusReparametrizedBall ha ha1 B).map '' Metric.ball 0 2 =
      B.map '' Metric.ball 0 (1 + a) := by
  change (B.map ∘ capRadialDiffeomorph 1 a ha ha1) '' Metric.ball 0 2 = _
  rw [Set.image_comp, capRadialDiffeomorph_ball_two ha ha1]

theorem annulusReparametrizedBall_center :
    (annulusReparametrizedBall ha ha1 B).map 0 = B.map 0 := by
  change B.map (capRadialMap (capRadialOrderIso 1 a ha ha1) 0) = B.map 0
  rw [capRadialMap_zero]

theorem annulusReparametrizedBall_positive (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (annulusReparametrizedBall ha ha1 B).map ((1 + s) • z.val) =
      B.map ((1 + a * s) • z.val) := by
  rw [annulusReparametrizedBall_map,
    capRadialDiffeomorph_smul ha ha1 z (1 + s) (by linarith [hs.1]),
    add_sub_cancel_left]

theorem annulusReparametrizedBall_negative (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    (annulusReparametrizedBall ha ha1 B).map ((1 - s) • z.val) =
      B.map ((1 - a * s) • z.val) := by
  have hs' : -s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  simpa only [sub_eq_add_neg, mul_neg] using
    annulusReparametrizedBall_positive ha ha1 B z hs'

include ha in

theorem annulusReparametrizedBall_inner_range (haquarter : a ≤ 1 / 4)
    (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(1 + a * s) • z.val‖ < 5 / 4 := by
  have hpos : 0 < 1 + a * s := add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg ha.le hs.1.le)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, show ‖z.val‖ = 1 by simp, mul_one]
  have hlt := mul_lt_mul_of_pos_left hs.2 ha
  linarith

end PoincareConjecture.M38
