import PoincareConjecture.Proofs.M38.EnclosingBallSubregions
import PoincareConjecture.Proofs.M38.ReciprocalSphereBall
import PoincareConjecture.Proofs.M38.SphereMonodromyComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} (C : SurgeryBallEmbedding A)
  (p : sphereCarrier.{u}.carrier) {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
  (B₀ B₁ : SurgeryBallEmbedding A)
  (hB₀ : B₀.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1)
  (hB₁ : B₁.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1)

local notation "D₀" => enclosingSphereBall B₀ C p ha ha8 hB₀
local notation "D₁" => enclosingSphereBall B₁ C p ha ha8 hB₁

theorem enclosingSphereTwoBallComplement_open : IsOpen ((D₀).closedBall ∪ (D₁).closedBall)ᶜ :=
  ((surgeryBall_closedImage_compact D₀ 1 (by norm_num)).isClosed.union
    (surgeryBall_closedImage_compact D₁ 1 (by norm_num)).isClosed).isOpen_compl

theorem reciprocalSphereBall_subset_twoBallComplement :
    (reciprocalSphereBall p ha ha8).map '' Metric.ball 0 2 ⊆
      ((D₀).closedBall ∪ (D₁).closedBall)ᶜ := by
  intro y hy hbad
  have hdis := Set.disjoint_left.mp (reciprocalSphereBall_full_disjoint p ha ha8) hy
  rcases hbad with hbad | hbad
  · exact hdis (enclosingSphereBall_inside_unit B₀ C p ha ha8 hB₀
      (surgeryBall_closedBall_subset_image D₀ hbad))
  · exact hdis (enclosingSphereBall_inside_unit B₁ C p ha ha8 hB₁
      (surgeryBall_closedBall_subset_image D₁ hbad))

variable
  (H : @OpenCylinderModel (sphereCarrier.{u}).carrier
    (sphereCarrier.{u}).topologicalSpace (sphereCarrier.{u}).chartedSpace
      ((enclosingSphereBall B₀ C p ha ha8 hB₀).closedBall ∪
        (enclosingSphereBall B₁ C p ha ha8 hB₁).closedBall)ᶜ)
  (beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

theorem monodromyLiftedZeroFiber_complement_open :
    IsOpen ((monodromyLiftedZeroFiber.{u} beta)ᶜ) := by
  rw [← monodromyLiftedCollar_central beta (1 / 4) (by norm_num)]
  exact (comparisonCentral_isClosed (monodromyLiftedCollar beta (1 / 4) (by norm_num))
    (by norm_num : (0 : ℝ) < 1 / 4) rfl).isOpen_compl

noncomputable def enclosingMonodromyBall : SurgeryBallEmbedding (monodromyCarrier.{u} beta) :=
  transportSurgeryBallRegion
    (A := sphereCarrier.{u}) (D := monodromyCarrier.{u} beta)
    (U := ((D₀).closedBall ∪ (D₁).closedBall)ᶜ)
    (V := (monodromyLiftedZeroFiber.{u} beta)ᶜ)
    (reciprocalSphereBall p ha ha8)
    (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta)
    (enclosingSphereTwoBallComplement_open C p ha ha8 B₀ B₁ hB₀ hB₁)
    (monodromyLiftedZeroFiber_complement_open beta)
    (reciprocalSphereBall_subset_twoBallComplement C p ha ha8 B₀ B₁ hB₀ hB₁)

theorem enclosingMonodromyBall_map (x : StandardCapSpace) :
    (enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta).map x =
      (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map
        ((reciprocalSphereBall p ha ha8).map x) := rfl

theorem enclosingMonodromyBall_closedBall :
    (enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta).closedBall =
      (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map ''
        (reciprocalSphereBall p ha ha8).closedBall :=
  transportSurgeryBallRegion_closedBall _ _ _ _ _

theorem enclosingMonodromyBall_avoids_zero :
    (enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta).closedBall ⊆
      (monodromyLiftedZeroFiber beta)ᶜ := by
  rw [enclosingMonodromyBall_closedBall]
  rintro _ ⟨x, hx, rfl⟩
  exact (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map_image.subset ⟨x,
    reciprocalSphereBall_subset_twoBallComplement C p ha ha8 B₀ B₁ hB₀ hB₁
      (surgeryBall_closedBall_subset_image (reciprocalSphereBall p ha ha8) hx), rfl⟩

theorem enclosingSphere_innerTwoHole_eq :
    ((D₀).closedBall ∪ (D₁).closedBall)ᶜ \ (reciprocalSphereBall p ha ha8).closedBall =
      enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁ := by
  change ((D₀).closedBall ∪ (D₁).closedBall)ᶜ ∩ (reciprocalSphereBall p ha ha8).closedBallᶜ =
    ((spherePoleReferenceBall p).map '' Metric.ball 0 (3 / 2)) ∩
      ((D₀).closedBall ∪ (D₁).closedBall)ᶜ
  rw [reciprocalSphereBall_complement, Set.inter_comm]

theorem enclosingMonodromyBall_complement :
    (enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta).closedBallᶜ =
      (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map ''
        enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁ ∪
          monodromyLiftedZeroFiber beta := by
  let F := sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta
  let D := enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta
  have hdiff : F.map '' enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁ =
      (monodromyLiftedZeroFiber beta)ᶜ \ D.closedBall := by
    rw [← enclosingSphere_innerTwoHole_eq C p ha ha8 B₀ B₁ hB₀ hB₁]
    exact transportSurgeryBallRegion_complement_image (reciprocalSphereBall p ha ha8) F
      (enclosingSphereTwoBallComplement_open C p ha ha8 B₀ B₁ hB₀ hB₁)
      (monodromyLiftedZeroFiber_complement_open beta)
      (reciprocalSphereBall_subset_twoBallComplement C p ha ha8 B₀ B₁ hB₀ hB₁)
  ext y
  constructor
  · intro hy
    by_cases hz : y ∈ monodromyLiftedZeroFiber beta
    · exact Or.inr hz
    · exact Or.inl (hdiff.symm ▸ ⟨hz, hy⟩)
  · rintro (hy | hy)
    · exact (hdiff.subset hy).2
    · exact fun hD => enclosingMonodromyBall_avoids_zero C p ha ha8 B₀ B₁ hB₀ hB₁ H beta hD hy

end PoincareConjecture.M38
