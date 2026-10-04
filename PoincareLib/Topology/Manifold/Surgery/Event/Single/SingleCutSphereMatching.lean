import PoincareLib.Topology.Manifold.Surgery.Event.Separating.SeparatingCut
import PoincareLib.Topology.Manifold.Surgery.Event.Enclosing.EnclosingBallSphere
import PoincareLib.Topology.Manifold.Surgery.Event.Enclosing.EnclosingBallSubregions
import PoincareLib.Topology.Manifold.Surgery.Event.Short.ShortCollarChart

/-!
# Exact annular matching for the actual single-cut collar

The shared-cut inverse is used only on its actual outer annulus. Its
original signed coordinates then agree with the supplied enclosing
sphere-ball coordinates after the same positive parameter scaling.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  (i : Fin (F.event T hT).cap_count) (hi : i ∉ S)

/-- The actual region inverse recovers the original signed ball point on its true outer annulus. -/
theorem singleCutRegionEquivalence_inverse_collar (positive : Bool) (z : UnitTwoSphere)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (singleCutRegionEquivalence F T hT P S i).inverse
      (uncutCollar F T hT P S i hi (cutSideReflection positive (z, s))) =
        (singleCutBall F T hT P S i positive).map (capAttachVector (z, s)) := by
  rw [singleCutRegionEquivalence_collar F T hT P S i hi positive z s hs]
  apply (singleCutRegionEquivalence F T hT P S i).left_inverse
  have hnorm := capAttachVector_mem (z := (z, s)) ⟨Set.mem_univ _, hs⟩
  let x : capDoubleBall := ⟨capAttachVector (z, s), by
    simpa only [capDoubleBall, TopologicalSpace.Opens.mem_mk, Metric.mem_ball, dist_zero_right]
      using hnorm.2⟩
  exact partialCapBall_annulus_mem_shared F T hT P S (insert i S) (Set.subset_insert i S)
    (⟨i, Set.mem_insert i S⟩, positive) x hnorm.1

variable (C : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)))

include hi in
/-- Every sufficiently short actual annulus lies in the inner enclosing chart and
outside both original closed balls, as certified by the exact shared-cut source. -/
theorem singleCutBall_annulus_mem_inner (positive : Bool)
    (hB : (singleCutBall F T hT P S i positive).map '' Metric.closedBall 0 (5 / 4) ⊆
      C.map '' Metric.ball 0 1)
    (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 4)) :
    (singleCutBall F T hT P S i positive).map (capAttachVector (z, s)) ∈
      enclosingInnerTwoHoleRegion C (singleCutBall F T hT P S i false)
        (singleCutBall F T hT P S i true) := by
  have hs1 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hnorm := capAttachVector_mem (z := (z, s)) ⟨Set.mem_univ _, hs1⟩
  let x : capDoubleBall := ⟨capAttachVector (z, s), by
    simpa only [capDoubleBall, TopologicalSpace.Opens.mem_mk, Metric.mem_ball, dist_zero_right]
      using hnorm.2⟩
  have hshared := partialCapBall_annulus_mem_shared F T hT P S (insert i S)
    (Set.subset_insert i S) (⟨i, Set.mem_insert i S⟩, positive) x hnorm.1
  have hsmall : capAttachVector (z, s) ∈ Metric.closedBall (0 : StandardCapSpace) (5 / 4) := by
    simp only [Metric.mem_closedBall, dist_zero_right, capAttachVector, norm_smul,
      Real.norm_eq_abs, abs_of_pos (show 0 < 1 + s by linarith [hs.1]),
      show ‖z.val‖ = 1 by simp, mul_one]
    linarith [hs.2]
  refine ⟨?_, (singleCut_sharedOpen F T hT P S i hi).subset hshared⟩
  exact (Set.image_mono (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 3 / 2)))
    (hB ⟨capAttachVector (z, s), hsmall, rfl⟩)

variable (p : sphereCarrier.{u}.carrier) {a b : ℝ}
  (ha : 0 < a) (ha8 : a ≤ 1 / 8) (hb : 0 < b) (hba : b < a)

include hb hba

/-- On the actual negative half, the enclosing-sphere map keeps the precise original
ball coordinate with the signed ratio of the two chosen collar scales. -/
theorem singleCutSphere_negative
    (hB₀ : (singleCutBall F T hT P S i false).map '' Metric.closedBall 0 (5 / 4) ⊆
      C.map '' Metric.ball 0 1)
    (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    (enclosingBallSphereCoordinates C p).map
      ((singleCutRegionEquivalence F T hT P S i).inverse
        (shortCollar (uncutCollar F T hT P S i hi) b (z, s))) =
      (enclosingSphereBall (singleCutBall F T hT P S i false) C p ha ha8 hB₀).map
        ((1 - (b / a) * s) • z.val) := by
  have hb1 : b < 1 := by linarith
  have hbs : b * s ∈ Set.Ioo (-1 : ℝ) 0 :=
    ⟨by nlinarith [mul_lt_mul_of_pos_left hs.1 hb], mul_neg_of_pos_of_neg hb hs.2⟩
  have hratio : 0 < b / a ∧ b / a < 1 :=
    ⟨div_pos hb ha, (div_lt_one ha).mpr hba⟩
  have hscaled : (b / a) * s ∈ Set.Ioo (-1 : ℝ) 0 :=
    ⟨by nlinarith [mul_lt_mul_of_pos_left hs.1 hratio.1],
      mul_neg_of_pos_of_neg hratio.1 hs.2⟩
  have heq : (singleCutRegionEquivalence F T hT P S i).inverse
      (shortCollar (uncutCollar F T hT P S i hi) b (z, s)) =
        (singleCutBall F T hT P S i false).map ((1 - b * s) • z.val) := by
    simpa only [shortCollar, cutSideReflection_apply, Bool.false_eq_true, ↓reduceIte,
      neg_neg, capAttachVector, sub_eq_add_neg] using
      singleCutRegionEquivalence_inverse_collar F T hT P S i hi false z (-(b * s))
        ⟨by linarith [hbs.2], by linarith [hbs.1]⟩
  rw [heq, enclosingSphereBall_negative (singleCutBall F T hT P S i false)
    C p ha ha8 hB₀ z hscaled]
  have hcancel : a * ((b / a) * s) = b * s := by
    rw [← mul_assoc, mul_div_cancel₀ _ ha.ne']
  change (spherePoleReferenceBall p).map
      (C.inverse ((singleCutBall F T hT P S i false).map ((1 - b * s) • z.val))) =
    (spherePoleReferenceBall p).map
      (C.inverse ((singleCutBall F T hT P S i false).map
        ((1 - a * ((b / a) * s)) • z.val)))
  rw [hcancel]

/-- On the actual positive half, the same maps and scale ratio give the original
positive ball coordinate, without changing its angular parameter. -/
theorem singleCutSphere_positive
    (hB₁ : (singleCutBall F T hT P S i true).map '' Metric.closedBall 0 (5 / 4) ⊆
      C.map '' Metric.ball 0 1)
    (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (enclosingBallSphereCoordinates C p).map
      ((singleCutRegionEquivalence F T hT P S i).inverse
        (shortCollar (uncutCollar F T hT P S i hi) b (z, s))) =
      (enclosingSphereBall (singleCutBall F T hT P S i true) C p ha ha8 hB₁).map
        ((1 + (b / a) * s) • z.val) := by
  have hb1 : b < 1 := by linarith
  have hbs : b * s ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hb hs.1, by nlinarith [mul_lt_mul_of_pos_left hs.2 hb]⟩
  have hratio : 0 < b / a ∧ b / a < 1 :=
    ⟨div_pos hb ha, (div_lt_one ha).mpr hba⟩
  have hscaled : (b / a) * s ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hratio.1 hs.1, by nlinarith [mul_lt_mul_of_pos_left hs.2 hratio.1]⟩
  have heq : (singleCutRegionEquivalence F T hT P S i).inverse
      (shortCollar (uncutCollar F T hT P S i hi) b (z, s)) =
        (singleCutBall F T hT P S i true).map ((1 + b * s) • z.val) := by
    simpa only [shortCollar, cutSideReflection_apply, ↓reduceIte, capAttachVector] using
      singleCutRegionEquivalence_inverse_collar F T hT P S i hi true z (b * s) hbs
  rw [heq, enclosingSphereBall_positive (singleCutBall F T hT P S i true)
    C p ha ha8 hB₁ z hscaled]
  have hcancel : a * ((b / a) * s) = b * s := by
    rw [← mul_assoc, mul_div_cancel₀ _ ha.ne']
  change (spherePoleReferenceBall p).map
      (C.inverse ((singleCutBall F T hT P S i true).map ((1 + b * s) • z.val))) =
    (spherePoleReferenceBall p).map
      (C.inverse ((singleCutBall F T hT P S i true).map
        ((1 + a * ((b / a) * s)) • z.val)))
  rw [hcancel]

include ha8 in
/-- Every noncentral point of the actual short collar belongs to the precise image
of the original inner two-hole region under the original shared-cut equivalence. -/
theorem singleCut_shortCollar_mem_inner_image
    (hB₀ : (singleCutBall F T hT P S i false).map '' Metric.closedBall 0 (5 / 4) ⊆
      C.map '' Metric.ball 0 1)
    (hB₁ : (singleCutBall F T hT P S i true).map '' Metric.closedBall 0 (5 / 4) ⊆
      C.map '' Metric.ball 0 1)
    (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) (hs0 : s ≠ 0) :
    shortCollar (uncutCollar F T hT P S i hi) b (z, s) ∈
      (singleCutRegionEquivalence F T hT P S i).map ''
        enclosingInnerTwoHoleRegion C (singleCutBall F T hT P S i false)
          (singleCutBall F T hT P S i true) := by
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · have hu : -(b * s) ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
      ⟨neg_pos.mpr (mul_neg_of_pos_of_neg hb hneg),
        by nlinarith [mul_lt_mul_of_pos_left hs.1 hb]⟩
    refine ⟨(singleCutBall F T hT P S i false).map (capAttachVector (z, -(b * s))),
      singleCutBall_annulus_mem_inner F T hT P S i hi C false hB₀ z hu, ?_⟩
    simpa only [shortCollar, cutSideReflection_apply, Bool.false_eq_true, ↓reduceIte,
      neg_neg] using
      (singleCutRegionEquivalence_collar F T hT P S i hi false z (-(b * s))
        ⟨hu.1, hu.2.trans (by norm_num)⟩).symm
  · have hu : b * s ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
      ⟨mul_pos hb hpos, by nlinarith [mul_lt_mul_of_pos_left hs.2 hb]⟩
    refine ⟨(singleCutBall F T hT P S i true).map (capAttachVector (z, b * s)),
      singleCutBall_annulus_mem_inner F T hT P S i hi C true hB₁ z hu, ?_⟩
    simpa only [shortCollar, cutSideReflection_apply, ↓reduceIte] using
      (singleCutRegionEquivalence_collar F T hT P S i hi true z (b * s)
        ⟨hu.1, hu.2.trans (by norm_num)⟩).symm

end PoincareMT.M38
