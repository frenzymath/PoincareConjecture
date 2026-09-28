import PoincareConjecture.Proofs.M38.SpherePunctureCoordinates
import PoincareConjecture.Proofs.M38.TwoBallAffineNormalization
import PoincareConjecture.Proofs.M38.RegionEquivalences

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

noncomputable def euclideanReferenceBall (a : StandardCapSpace) :
    SurgeryBallEmbedding euclideanCarrier.{u} := by
  let f : StandardCapSpace → euclideanCarrier.{u}.carrier := fun x => ULift.up (a + x)
  let g : euclideanCarrier.{u}.carrier → StandardCapSpace := fun y => y.down - a
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    (threeManifold_up_contMDiff StandardCapSpace).comp (contMDiff_const.add contMDiff_id)
  have hg : ContMDiff (𝓡 3) (𝓡 3) ∞ g :=
    (threeManifold_down_contMDiff StandardCapSpace).sub contMDiff_const
  have hleft : Set.LeftInvOn g f (Metric.ball (0 : StandardCapSpace) 2) := by
    intro x _
    exact add_sub_cancel_left a x
  exact {
    map := f
    inverse := g
    map_smooth := hf.contMDiffOn
    inverse_smooth := hg.contMDiffOn
    left_inverse := hleft
    right_inverse := by
      rintro y ⟨x, hx, rfl⟩
      exact congrArg f (hleft hx)
    open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball
      hf.contMDiffOn hg.contMDiffOn hleft }

theorem euclideanReferenceBall_map (a x : StandardCapSpace) :
    (euclideanReferenceBall.{u} a).map x = ULift.up (a + x) := rfl

theorem euclideanReferenceBall_inverse (a : StandardCapSpace)
    (y : euclideanCarrier.{u}.carrier) :
    (euclideanReferenceBall a).inverse y = y.down - a := rfl

theorem exists_euclideanBallAffineNormalizationCompact
    (B : SurgeryBallEmbedding euclideanCarrier.{u}) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3)
      euclideanCarrier.{u}.carrier euclideanCarrier.{u}.carrier ∞,
    ∃ L : StandardCapSpace ≃L[ℝ] StandardCapSpace,
    ∃ b : ℝ,
      (L : StandardCapSpace →L[ℝ] StandardCapSpace) =
        fderiv ℝ (fun x => (B.map x).down) 0 ∧
      0 < b ∧ b < 1 ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        (e (B.map x)).down = (B.map 0).down + L (b • x)) ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 → L (b • x) ∈ Metric.ball 0 2) ∧
      (∀ y : euclideanCarrier.{u}.carrier,
        y ∉ B.map '' Metric.closedBall 0 (3 / 2) → e y = y) := by
  let a := (B.map 0).down
  let C := euclideanReferenceBall.{u} a
  have hcenter : C.map 0 = B.map 0 := by
    apply ULift.ext
    exact add_zero a
  have hBC : B.map 0 ∈ C.map '' Metric.ball (0 : StandardCapSpace) 2 :=
    ⟨0, by simp, hcenter⟩
  have hzero : C.inverse (B.map 0) = 0 := sub_self a
  obtain ⟨e, L, b, hL, hb, hb1, he, hcoord, hfix⟩ :=
    exists_surgeryBallAffineNormalizationCompact B C hBC
  have hderivative : (L : StandardCapSpace →L[ℝ] StandardCapSpace) =
      fderiv ℝ (fun x => (B.map x).down) 0 := by
    calc
      _ = fderiv ℝ (fun x => (B.map x).down - a) 0 := hL
      _ = fderiv ℝ (fun x => (B.map x).down) 0 := fderiv_sub_const a
  refine ⟨e, L, b, hderivative, hb, hb1, ?_, ?_, hfix⟩
  · intro x hx
    have hm : (e (B.map x)).down = a + (C.inverse (B.map 0) + L (b • x)) :=
      congrArg ULift.down (he x hx)
    simpa only [hzero, zero_add] using hm
  · intro x hx
    simpa only [hzero, zero_add] using hcoord x hx

theorem exists_euclideanBallAffineNormalization
    (B : SurgeryBallEmbedding euclideanCarrier.{u}) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3)
      euclideanCarrier.{u}.carrier euclideanCarrier.{u}.carrier ∞,
    ∃ L : StandardCapSpace ≃L[ℝ] StandardCapSpace,
    ∃ b : ℝ,
      (L : StandardCapSpace →L[ℝ] StandardCapSpace) =
        fderiv ℝ (fun x => (B.map x).down) 0 ∧
      0 < b ∧ b < 1 ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        (e (B.map x)).down = (B.map 0).down + L (b • x)) ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 → L (b • x) ∈ Metric.ball 0 2) ∧
      (∀ y : euclideanCarrier.{u}.carrier, y ∉ B.map '' Metric.ball 0 2 → e y = y) := by
  obtain ⟨e, L, b, hL, hb, hb1, hinner, hcoord, hfix⟩ :=
    exists_euclideanBallAffineNormalizationCompact B
  refine ⟨e, L, b, hL, hb, hb1, hinner, hcoord, ?_⟩
  intro y hy
  exact hfix y (fun h => hy ((Set.image_mono
    (Metric.closedBall_subset_ball (by norm_num))) h))

variable (B : SurgeryBallEmbedding euclideanCarrier.{u})
  (e : Diffeomorph (𝓡 3) (𝓡 3)
    euclideanCarrier.{u}.carrier euclideanCarrier.{u}.carrier ∞)
  (L : StandardCapSpace ≃L[ℝ] StandardCapSpace) (b : ℝ) (hb : 0 < b)

section TargetCenter

variable (a : StandardCapSpace)
  (hinner : ∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
    (e (B.map x)).down = a + L (b • x))

include hb hinner

theorem euclideanBallAffine_closedImageAt :
    e '' B.closedBall =
      {y : euclideanCarrier.{u}.carrier | ‖L.symm (y.down - a)‖ ≤ b} := by
  apply Set.Subset.antisymm
  · rintro y ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    change ‖L.symm ((e (B.map x)).down - a)‖ ≤ b
    rw [hinner x (hxnorm.trans (by norm_num)), add_sub_cancel_left,
      L.symm_apply_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    nlinarith
  · intro y hy
    let x : StandardCapSpace := b⁻¹ • L.symm (y.down - a)
    have hxnorm : ‖x‖ ≤ 1 := by
      dsimp only [x]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
      calc
        b⁻¹ * ‖L.symm (y.down - a)‖ ≤ b⁻¹ * b :=
          mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hb.le)
        _ = 1 := inv_mul_cancel₀ hb.ne'
    have hlinear : L (b • x) = y.down - a := by
      dsimp only [x]
      rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul, L.apply_symm_apply]
    refine ⟨B.map x, ⟨x, ?_, rfl⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hxnorm
    · apply ULift.ext
      rw [hinner x (hxnorm.trans (by norm_num)), hlinear]
      abel

theorem euclideanBallAffine_complementImageAt :
    e '' B.closedBallᶜ =
      {y : euclideanCarrier.{u}.carrier | b < ‖L.symm (y.down - a)‖} := by
  rw [Set.image_compl_eq (f := fun y : euclideanCarrier.{u}.carrier => e y)
      ⟨e.injective, e.surjective⟩,
    euclideanBallAffine_closedImageAt B e L b hb a hinner]
  ext y
  change ¬ (‖L.symm (y.down - a)‖ ≤ b) ↔ b < ‖L.symm (y.down - a)‖
  exact not_le

end TargetCenter

variable (hinner : ∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
  (e (B.map x)).down = (B.map 0).down + L (b • x))

include hb hinner

theorem euclideanBallAffine_closedImage :
    e '' B.closedBall =
      {y : euclideanCarrier.{u}.carrier | ‖L.symm (y.down - (B.map 0).down)‖ ≤ b} :=
  euclideanBallAffine_closedImageAt B e L b hb (B.map 0).down hinner

theorem euclideanBallAffine_complementImage :
    e '' B.closedBallᶜ =
      {y : euclideanCarrier.{u}.carrier | b < ‖L.symm (y.down - (B.map 0).down)‖} :=
  euclideanBallAffine_complementImageAt B e L b hb (B.map 0).down hinner

theorem exists_euclideanBallEllipsoidEquivalence :
    ∃ E : SurgeryRegionEquivalence euclideanCarrier.{u} euclideanCarrier.{u}
      B.closedBallᶜ
      {y : euclideanCarrier.{u}.carrier | b < ‖L.symm (y.down - (B.map 0).down)‖},
      E.map = e ∧ E.inverse = e.symm := by
  have h : ∃ E : SurgeryRegionEquivalence euclideanCarrier.{u} euclideanCarrier.{u}
      B.closedBallᶜ (e '' B.closedBallᶜ), E.map = e ∧ E.inverse = e.symm :=
    ⟨diffeomorphRegions e B.closedBallᶜ, rfl, rfl⟩
  rwa [euclideanBallAffine_complementImage B e L b hb hinner] at h

end PoincareConjecture.M38
