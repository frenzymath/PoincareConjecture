import PoincareConjecture.Proofs.M38.IncidentCappingComparison
import PoincareConjecture.Proofs.M38.FiniteCappingGerms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem exists_incident_diffeomorph_of_matched_balls
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) (Q : GeneralizedSliceCarrier.{u})
    {U : Set Q.carrier}
    (E : SurgeryRegionEquivalence Q (componentCarrier (incidentOldCarrier F T hT) x) U univ)
    (B : incidentCapIndex F T hT P x → SurgeryBallEmbedding Q)
    (hBsep : ∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall)
    (hUB : U = (⋃ i, (B i).closedBall)ᶜ)
    (c : incidentCapIndex F T hT P x → RoundCylinderSpace → Q.carrier)
    (r δ : incidentCapIndex F T hT P x → ℝ)
    (hr : ∀ i, 0 < r i) (hδ : ∀ i, 0 < δ i)
    (hBmatch : ∀ i (z : UnitTwoSphere) (s : ℝ), |s| < r i →
      (B i).map ((1 + s) • z.val) = c i (z, s))
    (hcompare : ∀ i (z : UnitTwoSphere) (s : ℝ), 0 < s → s < δ i →
      (E.map (c i (z, s))).val.val = (P i.val).collar (z, s)) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    ∃ d : Diffeomorph (𝓡 3) (𝓡 3) Q.carrier A.carrier ∞,
      (∀ y ∈ U, d y = incidentOldInclusion F T hT P x (E.map y)) ∧
      ∀ i z, z ∈ Metric.closedBall 0 1 →
        d ((B i).map z) = (incidentCapBall F T hT P x i).map z := by
  classical
  let E' : SurgeryRegionEquivalence Q
      (componentCarrier (incidentOldCarrier F T hT) x) (⋃ i, (B i).closedBall)ᶜ univ := {
    map := E.map
    inverse := E.inverse
    map_image := by simpa only [← hUB] using E.map_image
    inverse_image := by simpa only [← hUB] using E.inverse_image
    left_inverse := by simpa only [← hUB] using E.left_inverse
    right_inverse := E.right_inverse
    map_smooth := by simpa only [← hUB] using E.map_smooth
    inverse_smooth := E.inverse_smooth }
  let C := incidentCapBall F T hT P x
  let J := incidentCappingComplementEquivalence F T hT P x Q B E'
  have hCsep (i j : incidentCapIndex F T hT P x) (hij : i ≠ j) :
      Disjoint (C i).closedBall (C j).closedBall :=
    (incidentCapBall_image_disjoint F T hT P x i j hij).mono
      (surgeryBall_closedBall_subset_image (C i)) (surgeryBall_closedBall_subset_image (C j))
  have hmatch (i : incidentCapIndex F T hT P x) : ∃ a : ℝ, 0 < a ∧
      ∀ (z : UnitTwoSphere) (s : ℝ), 0 < s → s < a →
        J.map ((B i).map ((1 + s) • z.val)) = (C i).map ((1 + s) • z.val) := by
    refine ⟨min (r i) (min (δ i) 1), lt_min (hr i) (lt_min (hδ i) zero_lt_one), ?_⟩
    intro z s hs hsa
    have hsr : s < r i := hsa.trans_le (min_le_left _ _)
    have hsδ : s < δ i := hsa.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hs1 : s < 1 := hsa.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hz := capAttachVector_mem (z := (z, s)) ⟨mem_univ _, hs, hs1⟩
    let w : capDoubleBall := ⟨capAttachVector (z, s),
      by
        change capAttachVector (z, s) ∈ Metric.ball 0 2
        simpa only [Metric.mem_ball, dist_zero_right] using hz.2⟩
    have hw : E.map (c i (z, s)) = incidentAttachmentPoint F T hT P x i w hz.1 := by
      apply Subtype.ext
      apply Subtype.ext
      change (E.map (c i (z, s))).val.val = ((P i.val).attachmentChart w).val
      exact (hcompare i z s hs hsδ).trans
        ((congrArg (P i.val).collar
          (capAttachCoordinates_vector (z := (z, s)) ⟨mem_univ _, hs, hs1⟩)).symm.trans
            ((P i.val).attachmentChart_apply (x := w) hz.1).symm)
    change (incidentOldRegionEquivalence F T hT P x).map
      (E.map ((B i).map ((1 + s) • z.val))) = (C i).map ((1 + s) • z.val)
    exact (congrArg (fun y => (incidentOldRegionEquivalence F T hT P x).map (E.map y))
      (hBmatch i z s (by simpa only [abs_of_pos hs] using hsr))).trans
        ((congrArg (incidentOldRegionEquivalence F T hT P x).map hw).trans
          (incidentOldRegionEquivalence_attachment F T hT P x i w hz.1))
  obtain ⟨d, hd, hball⟩ := exists_finiteCappingDiffeomorph_of_germs B C J hBsep hCsep hmatch
  exact ⟨d, fun y hy => hd y (hUB ▸ hy), hball⟩

end PoincareConjecture.M38
