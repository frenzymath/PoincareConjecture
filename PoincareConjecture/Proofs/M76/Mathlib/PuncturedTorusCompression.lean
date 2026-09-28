import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartCompression
import PoincareConjecture.Proofs.M76.Mathlib.SupportedPuncturedSquareCompression
import PoincareConjecture.Proofs.M76.Mathlib.TorusSquareCompactCore












set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip






theorem exists_punctured_torus_compression {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hdhalf : d < (4 * L) / 2) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    let Q := AddCircle.centeredSquareQuotient (4 * L)
    let K := {x : ℝ × ℝ | ‖x‖ ≤ (4 * L) / 2 - d / 2}
    ∃ (H : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
      (C : (AddCircle (4 * L) × AddCircle (4 * L)) →
        (AddCircle (4 * L) × AddCircle (4 * L))),
      H.source = {x | ‖x‖ ∈ Ioo 0 ((4 * L) / 2)} ∧
      H.target = {x | ‖x‖ ∈ Ioo ((4 * L) / 2 - d) ((4 * L) / 2)} ∧
      H ∈ piecewiseAffineGroupoid (ℝ × ℝ) ∧
      IsLocalHomeomorphOn C {Q 0}ᶜ ∧ MapsTo C {Q 0}ᶜ (crossingBandRegion L d) ∧
      EqOn C (Q.symm.trans (H.trans Q)) (Q.symm.trans (H.trans Q)).source ∧
      EqOn C id (Q '' K)ᶜ ∧ EqOn C id (crossingBandRegion L (d / 2)) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  let Q := AddCircle.centeredSquareQuotient (4 * L)
  let K := {x : ℝ × ℝ | ‖x‖ ≤ (4 * L) / 2 - d / 2}
  have hR : 0 < (4 * L) / 2 - d / 2 := by linarith
  have hRB : (4 * L) / 2 - d / 2 < (4 * L) / 2 := by linarith
  obtain ⟨H, hHS, hHT, hHPL, hHfix⟩ :=
    SquareShell.exists_supported_punctured_square_compression
      (r := (4 * L) / 2 - d) (R := (4 * L) / 2 - d / 2) (B := (4 * L) / 2)
      (by linarith) (by linarith) hRB
  have hK : IsCompact K := by
    simpa only [K, Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : ℝ × ℝ) ((4 * L) / 2 - d / 2)
  have hKS : K ⊆ Q.source :=
    AddCircle.closedSquare_subset_centeredSquareQuotient_source (4 * L) hRB
  have hzero : (0 : ℝ × ℝ) ∈ K := by
    change ‖(0 : ℝ × ℝ)‖ ≤ (4 * L) / 2 - d / 2
    simpa only [norm_zero] using hR.le
  have hsource : H.source = Q.source \ {0} := by
    rw [hHS, AddCircle.centeredSquareQuotient_source]
    ext x
    simp only [mem_ofPred_eq, mem_Ioo, mem_sdiff, mem_singleton_iff,
      norm_pos_iff, and_comm]
  have htarget : H.target ⊆ Q.source := by
    intro x hx
    rw [hHT] at hx
    rw [AddCircle.centeredSquareQuotient_source]
    exact hx.2
  have hfixed : EqOn H id (Q.source \ K) := by
    intro x hx
    apply hHfix
    have hxB : ‖x‖ < (4 * L) / 2 := by
      simpa only [Q, AddCircle.centeredSquareQuotient_source, mem_ofPred_eq] using hx.1
    have hxR : (4 * L) / 2 - d / 2 < ‖x‖ := lt_of_not_ge hx.2
    exact ⟨hxR.le, hxB.le⟩
  have himage : Q '' H.target ⊆ crossingBandRegion L d := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hHT] at hx
    exact (centeredSquareQuotient_mem_crossingBand_iff hL hd hdhalf hx.2).mpr hx.1
  have houtside : (Q '' K)ᶜ ⊆ crossingBandRegion L d :=
    compl_centeredSquareImage_subset_crossingBand hL hd hdhalf (by linarith)
  obtain ⟨C, hC, hCimage, hCchart, hCfix⟩ :=
    Q.exists_supported_chart_compression H hK hKS hzero hsource htarget hfixed himage houtside
  refine ⟨H, C, hHS, hHT, hHPL, hC, hCimage, hCchart, hCfix, ?_⟩
  exact hCfix.mono (crossingBand_subset_compl_centeredSquareImage hL
    (by linarith : 0 < d / 2) (by linarith) le_rfl)

end PLAnnularStrip
