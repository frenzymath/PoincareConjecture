import PoincareConjecture.Proofs.M38.SingleCutHandleRegion
import PoincareConjecture.Proofs.M38.SingleCutOuterRegions
import PoincareConjecture.Proofs.M38.SingleCutOuterCollar
import PoincareConjecture.Proofs.M38.SingleCutNeighborhood
import PoincareConjecture.Proofs.M38.AlignedSphereTwoBallCylinder
import PoincareConjecture.Proofs.M38.ShortCollarConnectedSum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  (i : Fin (F.event T hT).cap_count) (hi : i ∉ S)

include hi in

theorem singleCut_nonseparating_data
    (hsame : ConnectedComponents.mk ((singleCutBall F T hT P S i false).map 0) =
      ConnectedComponents.mk ((singleCutBall F T hT P S i true).map 0)) :
    ∃ beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      Nonempty (SmoothConnectedSumData (partialCappedCarrier F T hT P (insert i S))
        (monodromyCarrier.{u} beta) (partialCappedCarrier F T hT P S)) := by
  classical
  let A := partialCappedCarrier F T hT P (insert i S)
  let X := partialCappedCarrier F T hT P S
  let B₀ := singleCutBall F T hT P S i false
  let B₁ := singleCutBall F T hT P S i true
  obtain ⟨C, hC⟩ := singleCut_exists_enclosing_ball F T hT P S i hsame
  have hB₀ : B₀.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1 :=
    fun _ hx => hC (Or.inl hx)
  have hB₁ : B₁.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1 :=
    fun _ hx => hC (Or.inr hx)
  let p : sphereCarrier.{u}.carrier := ULift.up
    ⟨EuclideanSpace.single 0 (1 : ℝ), by simp⟩
  let a : ℝ := 1 / 8
  have ha : 0 < a := by norm_num [a]
  have ha8 : a ≤ 1 / 8 := le_rfl
  let D₀ := enclosingSphereBall B₀ C p ha ha8 hB₀
  let D₁ := enclosingSphereBall B₁ C p ha ha8 hB₁
  have hdis : Disjoint (D₀.map '' Metric.ball 0 2) (D₁.map '' Metric.ball 0 2) :=
    enclosingSphereBall_disjoint C p ha ha8 B₀ B₁ hB₀ hB₁
      (singleCutBall_images_disjoint F T hT P S i)
  obtain ⟨H, theta0, theta1, k, eta, hk, hk2, heta, heta8, hlower, hupper⟩ :=
    exists_alignedSphereTwoBallCylinder D₀ D₁ hdis
  let b : ℝ := a * eta / 2
  have hb : 0 < b := div_pos (mul_pos ha heta) (by norm_num)
  have hba : b < a := by
    dsimp only [b]
    have h := mul_le_mul_of_nonneg_left heta8 ha.le
    nlinarith
  have hbeta : b / a < eta := by
    dsimp only [b]
    rw [div_lt_iff₀ ha]
    nlinarith [mul_pos ha heta]
  let beta := attachingMonodromy theta0 theta1
    (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞)
  let DB := enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta
  let c := uncutCollar F T hT P S i hi
  let V : Set X.carrier := singleCutHandleOpen F T hT P S i C ∪ comparisonCentralSphere c
  obtain ⟨Q, hV, hQ⟩ := exists_singleCutHandleRegion F T hT P S i hi C p ha ha8
    hb hba hk hk2 heta8 hbeta hB₀ hB₁ H theta0 theta1 hlower hupper
  let D := reciprocalEnclosingBall C ha ha8
  let U := singleCutExteriorRegion F T hT P S i C ha ha8
  let E₀ := singleCutExteriorIdentify F T hT P S i hi C ha ha8 hB₀ hB₁
  let E₁ := reverseRegions Q
  let d := singleCutOuterCollar F T hT P S i C ha ha8
  have hd : d.source = Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    singleCutOuterCollar_source F T hT P S i hi C ha ha8 hB₀ hB₁
  have hcentral : d '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      singleCutOuterSphere F T hT P S i C :=
    singleCutOuterCollar_central F T hT P S i C ha ha8
  have hneg : ∀ z : UnitTwoSphere, ∀ s ∈ Set.Ioo (-1 : ℝ) 0,
      d (z, s) = E₀.map (D.map ((1 - s) • z.val)) := by
    intro z s hs
    exact singleCutOuterCollar_negative F T hT P S i C ha ha8 z hs
  have hpos : ∀ z : UnitTwoSphere, ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      d (z, s) = E₁.map (DB.map
        ((1 + s) • ((reciprocalSphereDirection p).symm z).val)) := by
    intro z s hs
    change d (z, s) = Q.inverse
      (DB.map ((1 + s) • ((reciprocalSphereDirection p).symm z).val))
    rw [enclosingMonodromyBall_map]
    rw [hQ _ (singleCutOuterCollar_positive_mem_inner F T hT P S i C ha ha8
      hB₀ hB₁ p z hs)]
    exact (singleCutOuterCollar_positive_comparison F T hT P S i C ha ha8 p z hs).symm
  refine ⟨beta, exists_connectedSumData_of_local_gluing D DB
    (singleCutExteriorRegion_open F T hT P S i hi C ha ha8 hB₀ hB₁) hV E₀ E₁
    (singleCutExteriorRegion_disjoint_handle F T hT P S i hi C ha ha8 hB₀ hB₁)
    (reciprocalSphereDirection p).symm d hd hneg hpos ?_ ?_ (by norm_num)⟩
  · rw [hcentral]
    exact singleCutOuterSphere_disjoint_regions F T hT P S i hi C ha ha8 hB₀ hB₁
  · rw [hcentral]
    exact singleCutOuterRegions_cover F T hT P S i hi C ha ha8 hB₀ hB₁

end PoincareConjecture.M38
