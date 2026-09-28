import PoincareConjecture.Proofs.M38.SingleCutSphereMatching
import PoincareConjecture.Proofs.M38.EnclosingMonodromyBall

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

variable (C : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)))

include hi in

theorem singleCut_innerTwoHole_subset_shared :
    enclosingInnerTwoHoleRegion C B₀ B₁ ⊆
      sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S) := by
  rw [singleCut_sharedOpen F T hT P S i hi]
  exact fun _ hx => hx.2

def singleCutHandleOpen : Set (X).carrier := (E).map '' enclosingInnerTwoHoleRegion C B₀ B₁

include hi in

theorem singleCutHandleOpen_open : IsOpen (singleCutHandleOpen F T hT P S i C) := by
  let e := regionPartialDiffeomorph E
    (sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S)).isOpen
    (sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S)).isOpen
  exact e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (enclosingInnerTwoHoleRegion_open C B₀ B₁)
    (singleCut_innerTwoHole_subset_shared F T hT P S i hi C)

theorem singleCutHandleOpen_disjoint_central :
    Disjoint (singleCutHandleOpen F T hT P S i C)
      (comparisonCentralSphere (uncutCollar F T hT P S i hi)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ hx
  have h := (E).map_image.subset ⟨y,
    singleCut_innerTwoHole_subset_shared F T hT P S i hi C hy, rfl⟩
  exact ((singleCut_targetOpen F T hT P S i hi).subset h) hx

variable (p : sphereCarrier.{u}.carrier) {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
  (hB₀ : (singleCutBall F T hT P S i false).map '' Metric.closedBall 0 (5 / 4) ⊆
    C.map '' Metric.ball 0 1)
  (hB₁ : (singleCutBall F T hT P S i true).map '' Metric.closedBall 0 (5 / 4) ⊆
    C.map '' Metric.ball 0 1)

local notation "D₀" => enclosingSphereBall B₀ C p ha ha8 hB₀
local notation "D₁" => enclosingSphereBall B₁ C p ha ha8 hB₁
local notation "W" => enclosingInnerTwoHoleRegion C B₀ B₁
local notation "WS" => enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁

variable (H : @OpenCylinderModel (sphereCarrier.{u}).carrier
    (sphereCarrier.{u}).topologicalSpace (sphereCarrier.{u}).chartedSpace
      ((enclosingSphereBall (singleCutBall F T hT P S i false) C p ha ha8 hB₀).closedBall ∪
        (enclosingSphereBall (singleCutBall F T hT P S i true) C p ha ha8 hB₁).closedBall)ᶜ)
  (beta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

def singleCutModelOpen : Set (monodromyCarrier.{u} beta).carrier :=
  (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map '' WS

theorem singleCutModelOpen_open :
    IsOpen (singleCutModelOpen F T hT P S i C p ha ha8 hB₀ hB₁ H beta) := by
  let e := regionPartialDiffeomorph (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta)
    (enclosingSphereTwoBallComplement_open C p ha ha8 B₀ B₁ hB₀ hB₁)
    (monodromyLiftedZeroFiber_complement_open beta)
  exact e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (enclosingSphereInnerTwoHoleRegion_open C p ha ha8 B₀ B₁ hB₀ hB₁)
    (fun _ hy => hy.2)

theorem singleCutModelOpen_disjoint_zero :
    Disjoint (singleCutModelOpen F T hT P S i C p ha ha8 hB₀ hB₁ H beta)
      (monodromyLiftedZeroFiber beta) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ hx
  exact ((sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map_image.subset
    ⟨y, hy.2, rfl⟩) hx

noncomputable def singleCutHandleCoordinates :
    SurgeryRegionEquivalence X (monodromyCarrier.{u} beta)
      (singleCutHandleOpen F T hT P S i C)
      (singleCutModelOpen F T hT P S i C p ha ha8 hB₀ hB₁ H beta) :=
  composeRegions (reverseRegions (restrictRegions E W
    (singleCut_innerTwoHole_subset_shared F T hT P S i hi C)))
    (composeRegions (enclosingSphereInnerTwoHoleEquivalence C p ha ha8 B₀ B₁ hB₀ hB₁)
      (restrictRegions (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta)
        WS (fun _ hy => hy.2)))

theorem singleCutHandleCoordinates_map (x : (X).carrier) :
    (singleCutHandleCoordinates F T hT P S i hi C p ha ha8 hB₀ hB₁ H beta).map x =
      (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map
        ((enclosingBallSphereCoordinates C p).map ((E).inverse x)) := rfl

theorem singleCutHandleCoordinates_inverse (y : (monodromyCarrier.{u} beta).carrier) :
    (singleCutHandleCoordinates F T hT P S i hi C p ha ha8 hB₀ hB₁ H beta).inverse y =
      (E).map ((enclosingBallSphereCoordinates C p).inverse
        ((sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).inverse y)) := rfl

theorem singleCutHandleCoordinates_inverse_model {y : sphereCarrier.{u}.carrier} (hy : y ∈ WS) :
    (singleCutHandleCoordinates F T hT P S i hi C p ha ha8 hB₀ hB₁ H beta).inverse
        ((sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).map y) =
      (E).map ((enclosingBallSphereCoordinates C p).inverse y) := by
  rw [singleCutHandleCoordinates_inverse,
    (sphereTwoBallMonodromyComparison.{u} D₀ D₁ H beta).left_inverse hy.2]

end PoincareConjecture.M38
