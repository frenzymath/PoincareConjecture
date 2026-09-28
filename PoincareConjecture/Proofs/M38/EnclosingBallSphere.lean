import PoincareConjecture.Proofs.M38.AnnulusReparametrization
import PoincareConjecture.Proofs.M38.BallRegionTransport
import PoincareConjecture.Proofs.M38.SpherePoleNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}}

noncomputable def enclosingBallSphereCoordinates (C : SurgeryBallEmbedding A)
    (p : sphereCarrier.{u}.carrier) :
    SurgeryRegionEquivalence A sphereCarrier.{u}
      (C.map '' Metric.ball 0 2) ((spherePoleReferenceBall p).map '' Metric.ball 0 2) := by
  let K := spherePoleReferenceBall p
  exact {
    map := fun x => K.map (C.inverse x)
    inverse := fun y => C.map (K.inverse y)
    map_image := by
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨C.inverse x, surgeryBall_inverse_mem C hx, rfl⟩
      · rintro _ ⟨z, hz, rfl⟩
        refine ⟨C.map z, ⟨z, hz, rfl⟩, ?_⟩
        change K.map (C.inverse (C.map z)) = K.map z
        rw [C.left_inverse hz]
    inverse_image := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact ⟨K.inverse y, surgeryBall_inverse_mem K hy, rfl⟩
      · rintro _ ⟨z, hz, rfl⟩
        refine ⟨K.map z, ⟨z, hz, rfl⟩, ?_⟩
        change C.map (K.inverse (K.map z)) = C.map z
        rw [K.left_inverse hz]
    left_inverse := by
      intro x hx
      change C.map (K.inverse (K.map (C.inverse x))) = x
      rw [K.left_inverse (surgeryBall_inverse_mem C hx), C.right_inverse hx]
    right_inverse := by
      intro y hy
      change K.map (C.inverse (C.map (K.inverse y))) = y
      rw [C.left_inverse (surgeryBall_inverse_mem K hy), K.right_inverse hy]
    map_smooth := K.map_smooth.comp C.inverse_smooth (fun _ hx => surgeryBall_inverse_mem C hx)
    inverse_smooth := C.map_smooth.comp K.inverse_smooth
      (fun _ hy => surgeryBall_inverse_mem K hy) }

theorem enclosingBallSphereCoordinates_map (C : SurgeryBallEmbedding A)
    (p : sphereCarrier.{u}.carrier) (x : A.carrier) :
    (enclosingBallSphereCoordinates C p).map x =
      ULift.up (threeSphereStereoInverse (-p.down) (C.inverse x)) := rfl

theorem enclosingBallSphereCoordinates_inverse (C : SurgeryBallEmbedding A)
    (p y : sphereCarrier.{u}.carrier) :
    (enclosingBallSphereCoordinates C p).inverse y =
      C.map (stereographic' 3 (-p.down) y.down) := rfl

theorem enclosingBallSphereCoordinates_chart (C : SurgeryBallEmbedding A)
    (p : sphereCarrier.{u}.carrier) {x : StandardCapSpace} (hx : x ∈ Metric.ball 0 2) :
    (enclosingBallSphereCoordinates C p).map (C.map x) = (spherePoleReferenceBall p).map x := by
  change (spherePoleReferenceBall p).map (C.inverse (C.map x)) = _
  rw [C.left_inverse hx]

theorem enclosingBallSphereCoordinates_unit_image (C : SurgeryBallEmbedding A)
    (p : sphereCarrier.{u}.carrier) :
    (enclosingBallSphereCoordinates C p).map '' (C.map '' Metric.ball 0 1) =
      (spherePoleReferenceBall p).map '' Metric.ball 0 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [enclosingBallSphereCoordinates_chart C p
      (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz)]
    exact ⟨z, hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨C.map z, ⟨z, hz, rfl⟩, enclosingBallSphereCoordinates_chart C p
      (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz)⟩

private theorem enclosingAnnulus_lt_one {a : ℝ} (ha8 : a ≤ 1 / 8) : a < 1 := by
  linarith

variable (B C : SurgeryBallEmbedding A) (p : sphereCarrier.{u}.carrier)
  {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
  (hBC : B.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1)

include ha ha8 hBC in

theorem enclosingShortBall_inside_unit :
    (annulusReparametrizedBall ha (enclosingAnnulus_lt_one ha8) B).map '' Metric.ball 0 2 ⊆
      C.map '' Metric.ball 0 1 := by
  rw [annulusReparametrizedBall_image]
  apply Set.Subset.trans (Set.image_mono ?_) hBC
  exact (Metric.ball_subset_ball (by linarith : 1 + a ≤ 5 / 4)).trans
    Metric.ball_subset_closedBall

include ha ha8 hBC in

theorem enclosingShortBall_inside_chart :
    (annulusReparametrizedBall ha (enclosingAnnulus_lt_one ha8) B).map '' Metric.ball 0 2 ⊆
      C.map '' Metric.ball 0 2 :=
  (enclosingShortBall_inside_unit B C ha ha8 hBC).trans
    (Set.image_mono (Metric.ball_subset_ball (by norm_num)))

include hBC in

theorem enclosingOriginalBall_inside_chart : B.closedBall ⊆ C.map '' Metric.ball 0 2 := by
  change B.map '' Metric.closedBall 0 1 ⊆ _
  exact ((Set.image_mono (Metric.closedBall_subset_closedBall
    (by norm_num : (1 : ℝ) ≤ 5 / 4))).trans hBC).trans
    (Set.image_mono (Metric.ball_subset_ball (by norm_num)))

noncomputable def enclosingSphereBall : SurgeryBallEmbedding sphereCarrier.{u} :=
  transportSurgeryBallRegion
    (annulusReparametrizedBall ha (enclosingAnnulus_lt_one ha8) B)
    (enclosingBallSphereCoordinates C p) (surgeryBall_image_open C)
    (surgeryBall_image_open (spherePoleReferenceBall p))
    (enclosingShortBall_inside_chart B C ha ha8 hBC)

theorem enclosingSphereBall_map (x : StandardCapSpace) :
    (enclosingSphereBall B C p ha ha8 hBC).map x =
      (spherePoleReferenceBall p).map
        (C.inverse (B.map (capRadialDiffeomorph 1 a ha (enclosingAnnulus_lt_one ha8) x))) := rfl

theorem enclosingSphereBall_closedBall :
    (enclosingSphereBall B C p ha ha8 hBC).closedBall =
      (enclosingBallSphereCoordinates C p).map '' B.closedBall := by
  unfold enclosingSphereBall
  rw [transportSurgeryBallRegion_closedBall, annulusReparametrizedBall_closedBall]

theorem enclosingSphereBall_inside_unit :
    (enclosingSphereBall B C p ha ha8 hBC).map '' Metric.ball 0 2 ⊆
      (spherePoleReferenceBall p).map '' Metric.ball 0 1 := by
  rw [← enclosingBallSphereCoordinates_unit_image C p]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(annulusReparametrizedBall ha (enclosingAnnulus_lt_one ha8) B).map x,
    enclosingShortBall_inside_unit B C ha ha8 hBC ⟨x, hx, rfl⟩, rfl⟩

theorem enclosingSphereBall_center :
    (enclosingSphereBall B C p ha ha8 hBC).map 0 =
      (enclosingBallSphereCoordinates C p).map (B.map 0) := by
  change (enclosingBallSphereCoordinates C p).map
    ((annulusReparametrizedBall ha (enclosingAnnulus_lt_one ha8) B).map 0) = _
  rw [annulusReparametrizedBall_center]

theorem enclosingSphereBall_positive (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (enclosingSphereBall B C p ha ha8 hBC).map ((1 + s) • z.val) =
      (spherePoleReferenceBall p).map (C.inverse (B.map ((1 + a * s) • z.val))) := by
  change (enclosingBallSphereCoordinates C p).map
    ((annulusReparametrizedBall ha (enclosingAnnulus_lt_one ha8) B).map ((1 + s) • z.val)) = _
  rw [annulusReparametrizedBall_positive ha (enclosingAnnulus_lt_one ha8) B z hs]
  rfl

theorem enclosingSphereBall_negative (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    (enclosingSphereBall B C p ha ha8 hBC).map ((1 - s) • z.val) =
      (spherePoleReferenceBall p).map (C.inverse (B.map ((1 - a * s) • z.val))) := by
  change (enclosingBallSphereCoordinates C p).map
    ((annulusReparametrizedBall ha (enclosingAnnulus_lt_one ha8) B).map ((1 - s) • z.val)) = _
  rw [annulusReparametrizedBall_negative ha (enclosingAnnulus_lt_one ha8) B z hs]
  rfl

variable (B₀ B₁ : SurgeryBallEmbedding A)
  (hB₀ : B₀.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1)
  (hB₁ : B₁.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1)

include hB₀ hB₁ in

theorem enclosingSphereBall_disjoint
    (hdisjoint : Disjoint (B₀.map '' Metric.ball 0 2) (B₁.map '' Metric.ball 0 2)) :
    Disjoint ((enclosingSphereBall B₀ C p ha ha8 hB₀).map '' Metric.ball 0 2)
      ((enclosingSphereBall B₁ C p ha ha8 hB₁).map '' Metric.ball 0 2) := by
  let D₀ := annulusReparametrizedBall ha (enclosingAnnulus_lt_one ha8) B₀
  let D₁ := annulusReparametrizedBall ha (enclosingAnnulus_lt_one ha8) B₁
  let E := enclosingBallSphereCoordinates C p
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
  have hmaps : E.map (D₀.map x) = E.map (D₁.map z) := hxy.trans hzy.symm
  have heq : D₀.map x = D₁.map z := E.left_inverse.injOn
    (enclosingShortBall_inside_chart B₀ C ha ha8 hB₀ ⟨x, hx, rfl⟩)
    (enclosingShortBall_inside_chart B₁ C ha ha8 hB₁ ⟨z, hz, rfl⟩) hmaps
  have hzero : D₀.map x ∈ B₀.map '' Metric.ball 0 2 :=
    ⟨_, annulusRadial_mapsTo ha (enclosingAnnulus_lt_one ha8) hx, rfl⟩
  have hone : D₁.map z ∈ B₁.map '' Metric.ball 0 2 :=
    ⟨_, annulusRadial_mapsTo ha (enclosingAnnulus_lt_one ha8) hz, rfl⟩
  exact Set.disjoint_left.mp hdisjoint hzero (heq.symm ▸ hone)

theorem enclosingSphere_twoHole_image :
    (enclosingBallSphereCoordinates C p).map ''
      ((C.map '' Metric.ball 0 2) \ (B₀.closedBall ∪ B₁.closedBall)) =
      ((spherePoleReferenceBall p).map '' Metric.ball 0 2) \
        ((enclosingSphereBall B₀ C p ha ha8 hB₀).closedBall ∪
          (enclosingSphereBall B₁ C p ha ha8 hB₁).closedBall) := by
  rw [enclosingSphereBall_closedBall, enclosingSphereBall_closedBall, ← Set.image_union]
  let E := enclosingBallSphereCoordinates C p
  have hballs : B₀.closedBall ∪ B₁.closedBall ⊆ C.map '' Metric.ball 0 2 :=
    Set.union_subset (enclosingOriginalBall_inside_chart B₀ C hB₀)
      (enclosingOriginalBall_inside_chart B₁ C hB₁)
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨E.map_image.subset ⟨x, hx.1, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    have heq : z = x := E.left_inverse.injOn (hballs hz) hx.1 hzx
    exact hx.2 (heq ▸ hz)
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := E.map_image.symm ▸ hy.1
    refine ⟨x, ⟨hx, ?_⟩, hxy⟩
    intro hxb
    exact hy.2 ⟨x, hxb, hxy⟩

noncomputable def enclosingSphereTwoHoleEquivalence :
    SurgeryRegionEquivalence A sphereCarrier.{u}
      ((C.map '' Metric.ball 0 2) \ (B₀.closedBall ∪ B₁.closedBall))
      (((spherePoleReferenceBall p).map '' Metric.ball 0 2) \
        ((enclosingSphereBall B₀ C p ha ha8 hB₀).closedBall ∪
          (enclosingSphereBall B₁ C p ha ha8 hB₁).closedBall)) where
  map := (enclosingBallSphereCoordinates C p).map
  inverse := (enclosingBallSphereCoordinates C p).inverse
  map_image := enclosingSphere_twoHole_image C p ha ha8 B₀ B₁ hB₀ hB₁
  inverse_image := by
    rw [← enclosingSphere_twoHole_image C p ha ha8 B₀ B₁ hB₀ hB₁]
    exact (enclosingBallSphereCoordinates C p).left_inverse.image_image' Set.diff_subset
  left_inverse := (enclosingBallSphereCoordinates C p).left_inverse.mono Set.diff_subset
  right_inverse := (enclosingBallSphereCoordinates C p).right_inverse.mono Set.diff_subset
  map_smooth := (enclosingBallSphereCoordinates C p).map_smooth.mono Set.diff_subset
  inverse_smooth := (enclosingBallSphereCoordinates C p).inverse_smooth.mono Set.diff_subset

theorem enclosingSphereTwoHoleEquivalence_map (x : A.carrier) :
    (enclosingSphereTwoHoleEquivalence C p ha ha8 B₀ B₁ hB₀ hB₁).map x =
      (spherePoleReferenceBall p).map (C.inverse x) := rfl

theorem enclosingSphereTwoHoleEquivalence_inverse (y : sphereCarrier.{u}.carrier) :
    (enclosingSphereTwoHoleEquivalence C p ha ha8 B₀ B₁ hB₀ hB₁).inverse y =
      C.map ((spherePoleReferenceBall p).inverse y) := rfl

end PoincareConjecture.M38
