import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedLowerEstimates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedLowerRoots
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedLowerRadialFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedLowerSlices
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedLowerRegularity









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D



theorem exists_nestedReference_lower_fillings :
    ∃ Binner Bouter : BallNeighborhoodChart E2 E2,
      Binner.chart.source = Set.univ ∧ Binner.chart.target = Set.univ ∧
      Bouter.chart.source = Set.univ ∧ Bouter.chart.target = Set.univ ∧
      (0 : E2) ∈ Binner.inside ∧
      Binner.closedRegion ⊆ Metric.ball (0 : E2) (1 / 2) ∧
      Metric.closedBall (0 : E2) (Real.sqrt 15 / 4) ⊆ Bouter.inside ∧
      Bouter.closedRegion ⊆ Metric.ball (0 : E2) (Real.sqrt 4095 / 64) ∧
      Binner.closedRegion ⊆ Bouter.inside ∧
      ∀ d : ℝ,
        {v : E2 | heightCoordinates.symm (v, 17 / 16 + d) ∈
            (nestedReferenceBallChart d).closedRegion} =
          Bouter.closedRegion \ Binner.inside ∧
        {v : E2 | heightCoordinates.symm (v, 17 / 16 + d) ∈
            (nestedReferenceBallChart d).inside} =
          Bouter.inside \ Binner.closedRegion ∧
        {v : E2 | heightCoordinates.symm (v, 17 / 16 + d) ∈
            (nestedReferenceBallChart d).boundary} =
          Binner.boundary ∪ Bouter.boundary ∧
        ∀ q : UnitTwoSphere,
          (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
              17 / 16 + d →
            mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
              (fun p : UnitTwoSphere =>
                (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2)
              q ≠ 0 := by
  classical
  obtain ⟨hr0, hr01, hr1, _, _, _⟩ := NestedReferenceLower.radial_estimates
  obtain ⟨ri, ro, hri, hro, hroots⟩ := NestedReferenceLower.exists_smooth_roots
  have hI (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      t ∈ Ioo (-3 / 2 : ℝ) (3 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hiBound (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      1 / 4 < ri t ∧ ri t < 2 := by
    have h := hroots t (hI t ht)
    exact ⟨h.1, h.2.1.trans (by norm_num)⟩
  have hoBound (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      1 / 4 < ro t ∧ ro t < 2 := by
    have h := hroots t (hI t ht)
    constructor
    · linarith [h.2.2.1]
    · exact (h.2.2.2.1.trans hr1).trans (by norm_num)
  obtain ⟨Bi, his, hit, _hiflow, _hi0, hi⟩ :=
    NestedReferenceLower.exists_radial_filling ri hri hiBound
  obtain ⟨Bo, hos, hot, _hoflow, _ho0, ho⟩ :=
    NestedReferenceLower.exists_radial_filling ro hro hoBound
  have hb (v : E2) :
      1 / 4 < ri (v 0 / ‖v‖) ∧ ri (v 0 / ‖v‖) < 1 / 2 ∧
      Real.sqrt 15 / 4 < ro (v 0 / ‖v‖) ∧
        ro (v 0 / ‖v‖) < Real.sqrt 4095 / 64 := by
    have h := hroots (v 0 / ‖v‖)
      (hI _ (NestedReferenceLower.slice_radial_tests v).1)
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hzero : (0 : E2) ∈ Bi.inside := by
    apply (hi 0).1.mpr
    have h := (hb 0).1
    simp only [norm_zero] at *
    linarith
  have hsmall : Bi.closedRegion ⊆ ball (0 : E2) (1 / 2) := by
    intro v hv
    exact mem_ball_zero_iff.mpr (((hi v).2.1.mp hv).trans_lt (hb v).2.1)
  have hlarge : closedBall (0 : E2) (Real.sqrt 15 / 4) ⊆ Bo.inside := by
    intro v hv
    exact (ho v).1.mpr ((mem_closedBall_zero_iff.mp hv).trans_lt (hb v).2.2.1)
  have houter : Bo.closedRegion ⊆ ball (0 : E2) (Real.sqrt 4095 / 64) := by
    intro v hv
    exact mem_ball_zero_iff.mpr (((ho v).2.1.mp hv).trans_lt (hb v).2.2.2)
  have hnested : Bi.closedRegion ⊆ Bo.inside := by
    intro v hv
    apply (ho v).1.mpr
    have hvsmall := mem_ball_zero_iff.mp (hsmall hv)
    linarith [(hb v).2.2.1]
  refine ⟨Bi, Bo, his, hit, hos, hot, hzero, hsmall, hlarge, houter, hnested, ?_⟩
  intro d
  have hclosed (v : E2) :
      heightCoordinates.symm (v, 17 / 16 + d) ∈ (nestedReferenceBallChart d).closedRegion ↔
        v ∈ Bo.closedRegion \ Bi.inside := by
    obtain ⟨ht, hf⟩ := NestedReferenceLower.slice_radial_tests v
    obtain ⟨_, _, _, hoU, _, _, hs, _, _⟩ := hroots _ (hI _ ht)
    change _ ↔ v ∈ Bo.closedRegion ∧ v ∉ Bi.inside
    rw [(hf d).1, (ho v).2.1, (hi v).1]
    constructor
    · rintro ⟨hr, hU⟩
      have hpair := (hs ‖v‖ ⟨norm_nonneg _, hr⟩).2.2.2.mp hU
      exact ⟨hpair.2, not_lt.mpr hpair.1⟩
    · rintro ⟨hout, hin⟩
      have hr : ‖v‖ ≤ 1 := hout.trans (hoU.trans hr1).le
      exact ⟨hr, (hs ‖v‖ ⟨norm_nonneg _, hr⟩).2.2.2.mpr ⟨le_of_not_gt hin, hout⟩⟩
  have hinside (v : E2) :
      heightCoordinates.symm (v, 17 / 16 + d) ∈ (nestedReferenceBallChart d).inside ↔
        v ∈ Bo.inside \ Bi.closedRegion := by
    obtain ⟨ht, hf⟩ := NestedReferenceLower.slice_radial_tests v
    obtain ⟨_, _, _, hoU, _, _, hs, _, _⟩ := hroots _ (hI _ ht)
    change _ ↔ v ∈ Bo.inside ∧ v ∉ Bi.closedRegion
    rw [(hf d).2.1, (ho v).1, (hi v).2.1]
    constructor
    · rintro ⟨hr, hU⟩
      have hpair := (hs ‖v‖ ⟨norm_nonneg _, hr⟩).2.2.1.mp hU
      exact ⟨hpair.2, not_le.mpr hpair.1⟩
    · rintro ⟨hout, hin⟩
      have hr : ‖v‖ ≤ 1 := (hout.trans (hoU.trans hr1)).le
      exact ⟨hr, (hs ‖v‖ ⟨norm_nonneg _, hr⟩).2.2.1.mpr ⟨lt_of_not_ge hin, hout⟩⟩
  have hboundary (v : E2) :
      heightCoordinates.symm (v, 17 / 16 + d) ∈ (nestedReferenceBallChart d).boundary ↔
        v ∈ Bi.boundary ∪ Bo.boundary := by
    obtain ⟨ht, hf⟩ := NestedReferenceLower.slice_radial_tests v
    obtain ⟨_, hiU, _, hoU, _, _, hs, _, _⟩ := hroots _ (hI _ ht)
    change _ ↔ v ∈ Bi.boundary ∨ v ∈ Bo.boundary
    rw [(hf d).2.2, (hi v).2.2, (ho v).2.2]
    constructor
    · rintro ⟨hr, hU⟩
      exact (hs ‖v‖ ⟨norm_nonneg _, hr⟩).1.mp hU
    · intro hv
      have hr : ‖v‖ ≤ 1 := by
        rcases hv with hv | hv
        · rw [hv]
          exact hiU.le.trans (by norm_num)
        · rw [hv]
          exact (hoU.trans hr1).le
      exact ⟨hr, (hs ‖v‖ ⟨norm_nonneg _, hr⟩).1.mpr hv⟩
  refine ⟨Set.ext hclosed, Set.ext hinside, Set.ext hboundary, ?_⟩
  intro q hq
  exact NestedReferenceLower.height_regular d q hq

end PoincareConjecture.M25.Topology3D
