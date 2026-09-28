import PoincareConjecture.Proofs.M38.SingleCutRegions
import PoincareConjecture.Proofs.M38.ReciprocalEnclosingCollar
import PoincareConjecture.Proofs.M38.EnclosingMonodromyBall











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

private theorem reciprocalPositiveRadius_bounds {a s : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    1 < (3 / 2) * ((1 + a * s / 2) / (1 + a * s)) ∧
      (3 / 2) * ((1 + a * s / 2) / (1 + a * s)) < 3 / 2 := by
  have hv : 0 < a * s := mul_pos ha hs.1
  have hv8 : a * s < 1 / 8 := by
    have h := mul_lt_mul_of_pos_left hs.2 ha
    linarith
  have hden : 0 < 1 + a * s := by linarith
  have hlo : (2 / 3 : ℝ) < (1 + a * s / 2) / (1 + a * s) :=
    (lt_div_iff₀ hden).mpr (by nlinarith)
  have hhi : (1 + a * s / 2) / (1 + a * s) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  constructor <;> nlinarith

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  (i : Fin (F.event T hT).cap_count) (hi : i ∉ S)

local notation "A" => partialCappedCarrier F T hT P (insert i S)
local notation "X" => partialCappedCarrier F T hT P S
local notation "B₀" => singleCutBall F T hT P S i false
local notation "B₁" => singleCutBall F T hT P S i true
local notation "E" => singleCutRegionEquivalence F T hT P S i
local notation "U" => sharedCutOpen F T hT P S (insert i S) (Set.subset_insert i S)
local notation "V" => sharedCutTargetOpen F T hT P S (insert i S) (Set.subset_insert i S)

variable (C : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)))
  {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)
  (hB₀ : (singleCutBall F T hT P S i false).map '' Metric.closedBall 0 (5 / 4) ⊆
    C.map '' Metric.ball 0 1)
  (hB₁ : (singleCutBall F T hT P S i true).map '' Metric.closedBall 0 (5 / 4) ⊆
    C.map '' Metric.ball 0 1)

include hi hB₀ hB₁ in

theorem singleCutOuterCollar_mem_shared {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    reciprocalEnclosingCollar C ha ha8 z ∈ U := by
  change reciprocalEnclosingCollar C ha ha8 z ∈ (U : Set (A).carrier)
  rw [singleCut_sharedOpen F T hT P S i hi]
  intro hbad
  have havoid := Set.disjoint_left.mp (reciprocalEnclosingCollar_full_disjoint_unit C ha ha8)
    (Set.mem_image_of_mem (reciprocalEnclosingCollar C ha ha8) hz)
  rcases hbad with hbad | hbad
  · exact havoid (hB₀ ((Set.image_mono
      (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 5 / 4))) hbad))
  · exact havoid (hB₁ ((Set.image_mono
      (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 5 / 4))) hbad))


noncomputable def singleCutOuterCollar :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace (X).carrier ∞ :=
  (reciprocalEnclosingCollar C ha ha8).trans
    (regionPartialDiffeomorph E (U).isOpen (V).isOpen)


theorem singleCutOuterCollar_apply (z : RoundCylinderSpace) :
    singleCutOuterCollar F T hT P S i C ha ha8 z =
      (E).map (reciprocalEnclosingCollar C ha ha8 z) := rfl


theorem singleCutOuterCollar_inverse (x : (X).carrier) :
    (singleCutOuterCollar F T hT P S i C ha ha8).symm x =
      (reciprocalEnclosingCollar C ha ha8).symm ((E).inverse x) := rfl

include hi hB₀ hB₁ in

theorem singleCutOuterCollar_source :
    (singleCutOuterCollar F T hT P S i C ha ha8).source =
      Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
  change (reciprocalEnclosingCollar C ha ha8).source ∩
    (reciprocalEnclosingCollar C ha ha8) ⁻¹' (U : Set (A).carrier) = _
  rw [reciprocalEnclosingCollar_source]
  apply Set.inter_eq_left.mpr
  intro z hz
  exact singleCutOuterCollar_mem_shared F T hT P S i hi C ha ha8 hB₀ hB₁ hz

include hi hB₀ hB₁ in

theorem singleCutOuterCollar_target :
    (singleCutOuterCollar F T hT P S i C ha ha8).target =
      (E).map '' ((reciprocalEnclosingCollar C ha ha8) ''
        (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  let d := singleCutOuterCollar F T hT P S i C ha ha8
  have himage : d '' d.source = d.target := d.toPartialEquiv.image_source_eq_target
  rw [singleCutOuterCollar_source F T hT P S i hi C ha ha8 hB₀ hB₁] at himage
  rw [← himage]
  change ((E).map ∘ reciprocalEnclosingCollar C ha ha8) ''
    (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) = _
  exact Set.image_comp _ _ _


theorem singleCutOuterCollar_central :
    singleCutOuterCollar F T hT P S i C ha ha8 '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      (E).map '' (C.map '' Metric.sphere 0 (3 / 2)) := by
  change ((E).map ∘ reciprocalEnclosingCollar C ha ha8) ''
    (Set.univ ×ˢ ({0} : Set ℝ)) = _
  rw [Set.image_comp, reciprocalEnclosingCollar_central C ha ha8]


theorem singleCutOuterCollar_negative (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    singleCutOuterCollar F T hT P S i C ha ha8 (z, s) =
      (E).map ((reciprocalEnclosingBall C ha ha8).map ((1 - s) • z.val)) := by
  rw [singleCutOuterCollar_apply, reciprocalEnclosingCollar_negative C ha ha8 z hs]

variable (p : sphereCarrier.{u}.carrier)

local notation "WS" => enclosingSphereInnerTwoHoleRegion C p ha ha8 B₀ B₁ hB₀ hB₁


theorem singleCutOuterCollar_positive_mem_inner (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (reciprocalSphereBall p ha ha8).map
      ((1 + s) • ((reciprocalSphereDirection p).symm z).val) ∈ WS := by
  let w := (reciprocalSphereDirection p).symm z
  have hball : (1 + s) • w.val ∈ Metric.ball (0 : StandardCapSpace) 2 := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith [hs.1] : 0 < 1 + s), show ‖w.val‖ = 1 by simp, mul_one]
    linarith [hs.2]
  refine ⟨?_, reciprocalSphereBall_subset_twoBallComplement C p ha ha8 B₀ B₁ hB₀ hB₁
    ⟨(1 + s) • w.val, hball, rfl⟩⟩
  rw [reciprocalSphereBall_positive p ha ha8 z hs]
  let r : ℝ := (3 / 2) * ((1 + a * s / 2) / (1 + a * s))
  have hr : 1 < r ∧ r < 3 / 2 := reciprocalPositiveRadius_bounds ha ha8 hs
  refine ⟨r • z.val, ?_, rfl⟩
  simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans hr.1), show ‖z.val‖ = 1 by simp, mul_one] using hr.2


theorem singleCutOuterCollar_positive_comparison (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (E).map ((enclosingBallSphereCoordinates C p).inverse
      ((reciprocalSphereBall p ha ha8).map
        ((1 + s) • ((reciprocalSphereDirection p).symm z).val))) =
          singleCutOuterCollar F T hT P S i C ha ha8 (z, s) := by
  rw [singleCutOuterCollar_apply]
  apply congrArg (E).map
  have hz : (z, s) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Set.mem_univ _, by linarith [hs.1], hs.2⟩
  have hcimage : reciprocalEnclosingCollar C ha ha8 (z, s) ∈ C.map '' Metric.ball 0 2 := by
    change reciprocalEnclosingCollarMap C a (z, s) ∈ C.map '' Metric.ball 0 2
    exact ⟨_, reciprocalEnclosingCollar_coordinate_mem ha ha8 hz, rfl⟩
  have hcoords := surgeryBall_inverse_mem C hcimage
  have hmatch := reciprocalEnclosingCollar_positive_reference C ha ha8 p z hs
  change C.map ((spherePoleReferenceBall p).inverse
    ((reciprocalSphereBall p ha ha8).map
      ((1 + s) • ((reciprocalSphereDirection p).symm z).val))) =
        reciprocalEnclosingCollar C ha ha8 (z, s)
  rw [← hmatch, (spherePoleReferenceBall p).left_inverse hcoords, C.right_inverse hcimage]

end PoincareConjecture.M38
