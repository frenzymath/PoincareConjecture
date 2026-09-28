import PoincareConjecture.Proofs.M38.SingleCutHandleCoordinates
import PoincareConjecture.Proofs.M38.CollarRegionComparison
import PoincareConjecture.Proofs.M38.MonodromyFramedCollar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  (i : Fin (F.event T hT).cap_count) (hi : i ∉ S)

local notation "A" => partialCappedCarrier F T hT P (insert i S)
local notation "X" => partialCappedCarrier F T hT P S
local notation "B₀" => singleCutBall F T hT P S i false
local notation "B₁" => singleCutBall F T hT P S i true
local notation "E" => singleCutRegionEquivalence F T hT P S i
local notation "c" => uncutCollar F T hT P S i hi

variable (C : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)))
  (p : sphereCarrier.{u}.carrier)
  {a b k eta : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
  (hb : 0 < b) (hba : b < a) (hk : 0 < k) (hk2 : k ≤ 1 / 2)
  (heta8 : eta ≤ 1 / 8) (hbeta : b / a < eta)
  (hB₀ : (singleCutBall F T hT P S i false).map '' Metric.closedBall 0 (5 / 4) ⊆
    C.map '' Metric.ball 0 1)
  (hB₁ : (singleCutBall F T hT P S i true).map '' Metric.closedBall 0 (5 / 4) ⊆
    C.map '' Metric.ball 0 1)

local notation "D₀" => enclosingSphereBall B₀ C p ha ha8 hB₀
local notation "D₁" => enclosingSphereBall B₁ C p ha ha8 hB₁
local notation "WS" => enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁

variable (H : @OpenCylinderModel (sphereCarrier.{u}).carrier
    (sphereCarrier.{u}).topologicalSpace (sphereCarrier.{u}).chartedSpace
      ((enclosingSphereBall (singleCutBall F T hT P S i false) C p ha ha8 hB₀).closedBall ∪
        (enclosingSphereBall (singleCutBall F T hT P S i true) C p ha ha8 hB₁).closedBall)ᶜ)
  (theta0 theta1 : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
  (hlower : ∀ z : UnitTwoSphere, ∀ s : ℝ, 0 < s → s < eta →
    H.inverse ((enclosingSphereBall (singleCutBall F T hT P S i true) C p ha ha8 hB₁).map
      ((1 + s) • z.val)) = (theta1 z, k * s))
  (hupper : ∀ z : UnitTwoSphere, ∀ s : ℝ, 0 < s → s < eta →
    H.inverse ((enclosingSphereBall (singleCutBall F T hT P S i false) C p ha ha8 hB₀).map
      ((1 + s) • z.val)) = (theta0 z, 1 - k * s))

local notation "beta" => attachingMonodromy theta0 theta1 (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞)
local notation "G" => singleCutHandleCoordinates F T hT P S i hi C p ha ha8 hB₀ hB₁ H beta
local notation "UA" => singleCutHandleOpen F T hT P S i C
local notation "VB" => singleCutModelOpen F T hT P S i C p ha ha8 hB₀ hB₁ H beta
local notation "DB" => enclosingMonodromyBall C p ha ha8 B₀ B₁ hB₀ hB₁ H beta

include ha ha8 hb hba hbeta hlower hupper in

theorem singleCutHandleCoordinates_matching (z : RoundCylinderSpace)
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) (hz0 : z.2 ≠ 0) :
    (G).map (shortCollar c b z) =
      monodromyLiftedCylinder beta (theta1 z.1, (k * (b / a)) * z.2) := by
  rw [singleCutHandleCoordinates_map]
  have hq : 0 < b / a := div_pos hb ha
  rcases lt_or_gt_of_ne hz0 with hs | hs
  · have hscaled : 0 < -(b / a) * z.2 := mul_pos_of_neg_of_neg (neg_neg_of_pos hq) hs
    have hscaled_top : -(b / a) * z.2 < eta := by
      have h := mul_lt_mul_of_pos_left hz.2.1 hq
      nlinarith
    rw [singleCutSphere_negative F T hT P S i hi C p ha ha8 hb hba hB₀ z.1
      ⟨hz.2.1, hs⟩]
    rw [sphereTwoBallMonodromyComparison_map,
      show 1 - (b / a) * z.2 = 1 + (-(b / a) * z.2) by ring,
      hupper z.1 (-(b / a) * z.2) hscaled hscaled_top,
      show 1 - k * (-(b / a) * z.2) = 1 + (k * (b / a)) * z.2 by ring,
      attachingMonodromy_negative]
    rfl
  · have hscaled : 0 < (b / a) * z.2 := mul_pos hq hs
    have hscaled_top : (b / a) * z.2 < eta :=
      (mul_lt_mul_of_pos_left hz.2.2 hq).trans_le (by simpa only [mul_one] using hbeta.le)
    rw [singleCutSphere_positive F T hT P S i hi C p ha ha8 hb hba hB₁ z.1
      ⟨hs, hz.2.2⟩]
    rw [sphereTwoBallMonodromyComparison_map,
      hlower z.1 ((b / a) * z.2) hscaled hscaled_top]
    rw [mul_assoc]

include ha ha8 hb hba hk hk2 heta8 hbeta hlower hupper in

theorem exists_singleCutHandleRegion :
    ∃ Q : SurgeryRegionEquivalence X (monodromyCarrier.{u} beta)
      (UA ∪ comparisonCentralSphere c) (DB).closedBallᶜ,
      IsOpen (UA ∪ comparisonCentralSphere c) ∧
      ∀ y ∈ WS, Q.inverse ((sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map y) =
        (E).map ((enclosingBallSphereCoordinates C p).inverse y) := by
  have hb1 : b ≤ 1 := by linarith
  have hspeed : 0 < k * (b / a) := mul_pos hk (div_pos hb ha)
  have hwidth : 2 * ((k * (b / a)) * 1) ≤ 1 := by
    have hq : 0 < b / a := div_pos hb ha
    have hq8 : b / a < 1 / 8 := hbeta.trans_le heta8
    nlinarith [mul_le_mul_of_nonneg_left hk2 hq.le]
  let cA := shortCollarChart c hb hb1 (uncutCollar_source F T hT P S i hi)
  let cB := monodromyFramedCollar beta theta1 hspeed 1 hwidth
  have hcA : cA.source = Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := rfl
  have hcB : cB.source = Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    monodromyFramedCollar_source beta theta1 hspeed 1 hwidth
  have hcentA : comparisonCentralSphere cA = comparisonCentralSphere c :=
    shortCollarChart_central c hb hb1 (uncutCollar_source F T hT P S i hi)
  have hcentB : comparisonCentralSphere cB = monodromyLiftedZeroFiber beta :=
    monodromyFramedCollar_central beta theta1 hspeed 1 hwidth
  have hUA : Disjoint UA (comparisonCentralSphere cA) := by
    rw [hcentA]
    exact singleCutHandleOpen_disjoint_central F T hT P S i hi C
  have hVB : Disjoint VB (comparisonCentralSphere cB) := by
    rw [hcentB]
    exact singleCutModelOpen_disjoint_zero F T hT P S i C p ha ha8 hB₀ hB₁ H beta
  have hmatch : ∀ z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1, z.2 ≠ 0 → (G).map (cA z) = cB z := by
    intro z hz hz0
    exact singleCutHandleCoordinates_matching F T hT P S i hi C p ha ha8 hb hba hbeta
      hB₀ hB₁ H theta0 theta1 hlower hupper z hz hz0
  have hpunctA : ∀ z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1, z.2 ≠ 0 → cA z ∈ UA := by
    intro z hz hz0
    exact singleCut_shortCollar_mem_inner_image F T hT P S i hi C ha8 hb hba hB₀ hB₁
      z.1 hz.2 hz0
  have hpunctB : ∀ z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1, z.2 ≠ 0 → cB z ∈ VB := by
    intro z hz hz0
    rw [← hmatch z hz hz0]
    exact (G).map_image.subset ⟨cA z, hpunctA z hz hz0, rfl⟩
  have hUopen : IsOpen UA := singleCutHandleOpen_open F T hT P S i hi C
  have hVopen : IsOpen VB := singleCutModelOpen_open F T hT P S i C p ha ha8 hB₀ hB₁ H beta
  let Q' := collarRegionComparison cA cB G (by norm_num : (0 : ℝ) < 1)
    hcA hcB hUA hVB hpunctA hpunctB hmatch hUopen hVopen
  have hsrc : UA ∪ comparisonCentralSphere cA = UA ∪ comparisonCentralSphere c := by
    rw [hcentA]
  have htgt : VB ∪ comparisonCentralSphere cB = (DB).closedBallᶜ := by
    rw [hcentB]
    exact (enclosingMonodromyBall_complement C p ha ha8 B₀ B₁ hB₀ hB₁ H beta).symm
  let Q : SurgeryRegionEquivalence X (monodromyCarrier.{u} beta)
      (UA ∪ comparisonCentralSphere c) (DB).closedBallᶜ := {
    map := Q'.map
    inverse := Q'.inverse
    map_image := by rw [← hsrc, ← htgt]; exact Q'.map_image
    inverse_image := by rw [← hsrc, ← htgt]; exact Q'.inverse_image
    left_inverse := by rw [← hsrc]; exact Q'.left_inverse
    right_inverse := by rw [← htgt]; exact Q'.right_inverse
    map_smooth := by rw [← hsrc]; exact Q'.map_smooth
    inverse_smooth := by rw [← htgt]; exact Q'.inverse_smooth }
  refine ⟨Q, ?_, ?_⟩
  · rw [← hsrc]
    exact collarRegion_isOpen cA (by norm_num : (0 : ℝ) < 1) hcA hpunctA hUopen
  · intro y hy
    have hnot : (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map y ∉
        comparisonCentralSphere cB := by
      rw [hcentB]
      exact (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map_image.subset ⟨y, hy.2, rfl⟩
    change collarRegionComparisonMap cB cA (reverseRegions G)
      ((sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map y) = _
    rw [collarRegionComparisonMap_off cB cA (reverseRegions G) hnot]
    exact singleCutHandleCoordinates_inverse_model F T hT P S i hi C p ha ha8 hB₀ hB₁
      H beta hy

end PoincareConjecture.M38
