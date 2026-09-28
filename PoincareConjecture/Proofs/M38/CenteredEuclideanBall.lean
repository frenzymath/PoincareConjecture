import PoincareConjecture.Proofs.M38.EuclideanBallCylinder
import PoincareConjecture.Proofs.M38.OpenPointMotion










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold



theorem exists_euclideanBallCenterMotion
    (B : SurgeryBallEmbedding euclideanCarrier.{u}) :
    ∃ d : Diffeomorph (𝓡 3) (𝓡 3)
      euclideanCarrier.{u}.carrier euclideanCarrier.{u}.carrier ∞,
    ∃ R : ℝ, 0 < R ∧
      d (B.map 0) = ULift.up 0 ∧
      ∀ y : euclideanCarrier.{u}.carrier, R ≤ ‖y.down‖ → d y = y := by
  let R : ℝ := ‖(B.map 0).down‖ + 1
  let O : Set euclideanCarrier.{u}.carrier := {y | ‖y.down‖ < R}
  have hR : 0 < R := by dsimp only [R]; positivity
  have hO : IsOpen O := isOpen_lt
    (continuous_norm.comp continuous_uliftDown) continuous_const
  have heq : (ULift.up : StandardCapSpace → euclideanCarrier.{u}.carrier) ''
      Metric.ball 0 R = O := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ‖x‖ < R
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    · intro hy
      refine ⟨y.down, ?_, rfl⟩
      change ‖y.down‖ < R at hy
      simpa only [Metric.mem_ball, dist_zero_right] using hy
  have hconn : IsPreconnected O := by
    rw [← heq]
    exact (convex_ball (0 : StandardCapSpace) R).isPreconnected.image _
      continuous_uliftUp.continuousOn
  have hp : B.map 0 ∈ O := by
    change ‖(B.map 0).down‖ < ‖(B.map 0).down‖ + 1
    linarith
  have hzero : (ULift.up 0 : euclideanCarrier.{u}.carrier) ∈ O := by
    change ‖(0 : StandardCapSpace)‖ < R
    simpa only [norm_zero] using hR
  obtain ⟨d, hd, hfix⟩ := exists_diffeomorph_in_connected_open hO hconn
    (B.map 0) hp (ULift.up 0) hzero
  refine ⟨d, R, hR, hd, ?_⟩
  intro y hy
  exact hfix y (not_lt.mpr hy)


theorem surgeryBall_exists_euclideanCompactBound
    (B : SurgeryBallEmbedding euclideanCarrier.{u}) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ B.map '' Metric.closedBall 0 (3 / 2), ‖y.down‖ ≤ R := by
  have hc : IsCompact ((ULift.down : euclideanCarrier.{u}.carrier → StandardCapSpace) ''
      (B.map '' Metric.closedBall 0 (3 / 2))) :=
    (surgeryBall_closedImage_compact B (3 / 2) (by norm_num)).image continuous_uliftDown
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_le
  exact ⟨R, hR, fun y hy => hbound y.down ⟨y, hy, rfl⟩⟩




theorem exists_centeredEuclideanBallNormalization
    (B : SurgeryBallEmbedding euclideanCarrier.{u}) :
    ∃ d e : Diffeomorph (𝓡 3) (𝓡 3)
      euclideanCarrier.{u}.carrier euclideanCarrier.{u}.carrier ∞,
    ∃ L : StandardCapSpace ≃L[ℝ] StandardCapSpace,
    ∃ b R : ℝ,
      d (B.map 0) = ULift.up 0 ∧
      (L : StandardCapSpace →L[ℝ] StandardCapSpace) =
        fderiv ℝ (fun x => (d (B.map x)).down) 0 ∧
      0 < b ∧ b < 1 ∧ 0 < R ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        (e (B.map x)).down = L (b • x)) ∧
      (∀ y : euclideanCarrier.{u}.carrier, R ≤ ‖y.down‖ → e y = y) ∧
      (∀ y : euclideanCarrier.{u}.carrier, R ≤ ‖y.down‖ → e.symm y = y) := by
  obtain ⟨d, R₀, hR₀, hd0, hdfix⟩ := exists_euclideanBallCenterMotion B
  let D := transportSurgeryBall B d
  have hD0 : (D.map 0).down = 0 := congrArg ULift.down hd0
  obtain ⟨k, L, b, hL, hb, hb1, hinner, _, hkfix⟩ :=
    exists_euclideanBallAffineNormalizationCompact D
  obtain ⟨S, hS, hbound⟩ := surgeryBall_exists_euclideanCompactBound D
  let e := d.trans k
  let R := max R₀ (S + 1)
  have hR : 0 < R := hR₀.trans_le (le_max_left _ _)
  have hfix (y : euclideanCarrier.{u}.carrier) (hy : R ≤ ‖y.down‖) : e y = y := by
    change k (d y) = y
    rw [hdfix y ((le_max_left _ _).trans hy)]
    apply hkfix y
    intro hymem
    have hupper := hbound y hymem
    have hlower : S + 1 ≤ ‖y.down‖ := (le_max_right _ _).trans hy
    linarith
  refine ⟨d, e, L, b, R, hd0, hL, hb, hb1, hR, ?_, hfix, ?_⟩
  · intro x hx
    change (k (D.map x)).down = L (b • x)
    simpa only [hD0, zero_add] using hinner x hx
  · intro y hy
    apply e.injective
    change e (e.symm y) = e y
    rw [e.apply_symm_apply, hfix y hy]




theorem exists_centeredEuclideanBallCylinder
    (B : SurgeryBallEmbedding euclideanCarrier.{u}) :
    ∃ C : OpenCylinderModel B.closedBallᶜ,
    ∃ L : StandardCapSpace ≃L[ℝ] StandardCapSpace,
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      (∀ z : UnitTwoSphere, ∀ t : ℝ, 1 < t → t ≤ 5 / 4 →
        C.inverse (B.map (t • z.val)) = (linearSphereDiffeomorph L z, 1 - 1 / t)) ∧
      (∀ z : UnitTwoSphere, ∀ t : ℝ, 1 < t → t ≤ 5 / 4 →
        C.coordinate (linearSphereDiffeomorph L z, 1 - 1 / t) = B.map (t • z.val)) ∧
      (∀ y : euclideanCarrier.{u}.carrier, R ≤ ‖y.down‖ →
        C.inverse y = (capUnitDirection y.down, 1 - r / ‖y.down‖)) ∧
      (∀ z : UnitTwoSphere, ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → R ≤ r / (1 - s) →
        C.coordinate (z, s) = ULift.up ((r / (1 - s)) • z.val)) := by
  obtain ⟨d, e, L, b, R₀, hd0, hL, hb, hb1, hR₀, hinner, hfix, _⟩ :=
    exists_centeredEuclideanBallNormalization B
  let ρ : ℝ := ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ * b + 1
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hsize : ‖(L : StandardCapSpace →L[ℝ] StandardCapSpace)‖ * b ≤ ρ := by
    dsimp only [ρ]
    linarith
  have hinner0 : ∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
      (e (B.map x)).down = 0 + L (b • x) := by
    intro x hx
    simpa only [zero_add] using hinner x hx
  let C := euclideanBallCylinder B e L 0 hb hρ hsize hinner0
  let r : ℝ := directionalRadialScale L * b
  have hr : 0 < r := mul_pos (directionalRadialScale_pos L) hb
  let R : ℝ := max R₀ ((3 / 2) * ρ) + r + 1
  have hR₀R : R₀ ≤ R := by
    dsimp only [R]
    nlinarith [le_max_left R₀ ((3 / 2) * ρ)]
  have hρR : (3 / 2) * ρ ≤ R := by
    dsimp only [R]
    nlinarith [le_max_right R₀ ((3 / 2) * ρ)]
  have hrR : r < R := by
    dsimp only [R]
    nlinarith [le_max_left R₀ ((3 / 2) * ρ)]
  refine ⟨C, L, r, R, hr, hrR, ?_, ?_, ?_, ?_⟩
  · intro z t ht htop
    exact euclideanBallCylinder_inner_inverse B e L 0 hb hρ hsize hinner0 z ht htop
  · intro z t ht htop
    exact euclideanBallCylinder_inner_coordinate B e L 0 hb hρ hsize hinner0 z ht htop
  · intro y hy
    have hrad : (3 / 2) * ρ ≤ ‖y.down - 0‖ := by
      simpa only [sub_zero] using hρR.trans hy
    simpa only [sub_zero] using
      euclideanBallCylinder_outer_inverse B e L 0 hb hρ hsize hinner0 y
        (hfix y (hR₀R.trans hy)) hrad
  · intro z s hs hfar
    have hrad0 : 0 < r / (1 - s) := div_pos hr (sub_pos.mpr hs.2)
    have hnorm : ‖(r / (1 - s)) • z.val‖ = r / (1 - s) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrad0,
        show ‖z.val‖ = 1 by simp, mul_one]
    have hef : e (ULift.up (0 + (r / (1 - s)) • z.val)) =
        ULift.up (0 + (r / (1 - s)) • z.val) := by
      apply hfix
      change R₀ ≤ ‖(0 : StandardCapSpace) + (r / (1 - s)) • z.val‖
      rw [zero_add, hnorm]
      exact hR₀R.trans hfar
    simpa only [zero_add] using
      euclideanBallCylinder_outer_coordinate B e L 0 hb hρ hsize hinner0 z s hef hs
        (hρR.trans hfar)

end PoincareConjecture.M38
