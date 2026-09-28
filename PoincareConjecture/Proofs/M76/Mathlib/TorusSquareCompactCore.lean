import PoincareConjecture.Proofs.M76.Mathlib.TorusSquareBandRegion

set_option autoImplicit false

open Set

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

theorem closedSquare_subset_centeredSquareQuotient_source {R : ℝ} (hR : R < p / 2) :
    {x : ℝ × ℝ | ‖x‖ ≤ R} ⊆ (centeredSquareQuotient p).source := by
  intro x hx
  rw [centeredSquareQuotient_source]
  exact hx.trans_lt hR

theorem isCompact_centeredSquareQuotient_closedSquare {R : ℝ} (hR : R < p / 2) :
    IsCompact (centeredSquareQuotient p '' {x : ℝ × ℝ | ‖x‖ ≤ R}) := by
  have hK : IsCompact {x : ℝ × ℝ | ‖x‖ ≤ R} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : ℝ × ℝ) R
  exact hK.image_of_continuousOn ((centeredSquareQuotient p).continuousOn_toFun.mono
    (closedSquare_subset_centeredSquareQuotient_source p hR))

end AddCircle

namespace PLAnnularStrip

theorem crossingBand_subset_compl_centeredSquareImage {L d R : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hdhalf : d < (4 * L) / 2)
    (hR : R ≤ (4 * L) / 2 - d) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    crossingBandRegion L d ⊆
      (AddCircle.centeredSquareQuotient (4 * L) '' {x : ℝ × ℝ | ‖x‖ ≤ R})ᶜ := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  intro z hz
  rintro ⟨x, hx, rfl⟩
  have hxB : ‖x‖ < (4 * L) / 2 := lt_of_le_of_lt hx (by linarith)
  have hxband := (centeredSquareQuotient_mem_crossingBand_iff hL hd hdhalf hxB).mp hz
  exact (not_lt_of_ge (le_trans hx hR)) hxband

theorem compl_centeredSquareImage_subset_crossingBand {L d R : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hdhalf : d < (4 * L) / 2)
    (hR : (4 * L) / 2 - d ≤ R) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    (AddCircle.centeredSquareQuotient (4 * L) '' {x : ℝ × ℝ | ‖x‖ ≤ R})ᶜ ⊆
      crossingBandRegion L d := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  let Q := AddCircle.centeredSquareQuotient (4 * L)
  intro z hz
  by_cases hzQ : z ∈ Q.target
  · have hxQ : Q.symm z ∈ Q.source := Q.map_target hzQ
    have hxB : ‖Q.symm z‖ < (4 * L) / 2 := by
      simpa only [Q, AddCircle.centeredSquareQuotient_source, mem_ofPred_eq] using hxQ
    have hxR : R < ‖Q.symm z‖ := by
      by_contra h
      exact hz ⟨Q.symm z, le_of_not_gt h, Q.right_inv hzQ⟩
    have hband := (centeredSquareQuotient_mem_crossingBand_iff hL hd hdhalf hxB).mpr
      (hR.trans_lt hxR)
    change Q (Q.symm z) ∈ crossingBandRegion L d at hband
    simpa only [Q.right_inv hzQ] using hband
  · exact outside_centeredSquareQuotient_mem_crossingBand hL hd z hzQ

end PLAnnularStrip
