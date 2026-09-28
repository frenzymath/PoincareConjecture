import PoincareConjecture.Proofs.M76.Mathlib.PuncturedCubeCompression
import PoincareConjecture.Proofs.M76.Mathlib.TorusCubeBandRegion
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartCompression











set_option autoImplicit false

open Set Geometry

namespace TorusCube






theorem exists_punctured_three_torus_compression (p : ℝ) [Fact (0 < p)]
    {d : ℝ} (hd : 0 < d) (hdhalf : d < p / 2) :
    let Q := AddCircle.centeredCubeQuotient p
    let K := {x : CubeShell.Ambient | ‖x‖ ≤ p / 2 - d / 2}
    ∃ (H : OpenPartialHomeomorph CubeShell.Ambient CubeShell.Ambient)
      (C : ((AddCircle p × AddCircle p) × AddCircle p) →
        ((AddCircle p × AddCircle p) × AddCircle p)),
      H.source = {x | ‖x‖ ∈ Ioo 0 (p / 2)} ∧
      H.target = {x | ‖x‖ ∈ Ioo (p / 2 - d) (p / 2)} ∧
      H ∈ piecewiseAffineGroupoid CubeShell.Ambient ∧
      IsLocalHomeomorphOn C {Q 0}ᶜ ∧ MapsTo C {Q 0}ᶜ (crossingBands p d) ∧
      EqOn C (Q.symm.trans (H.trans Q)) (Q.symm.trans (H.trans Q)).source ∧
      EqOn C id (Q '' K)ᶜ ∧ EqOn C id (crossingBands p (d / 2)) := by
  let Q := AddCircle.centeredCubeQuotient p
  let K := {x : CubeShell.Ambient | ‖x‖ ≤ p / 2 - d / 2}
  have hR : 0 < p / 2 - d / 2 := by linarith
  have hRB : p / 2 - d / 2 < p / 2 := by linarith
  obtain ⟨H, hHS, hHT, hHPL, hHfix⟩ :=
    CubeShell.exists_supported_punctured_cube_compression
      (r := p / 2 - d) (R := p / 2 - d / 2) (B := p / 2)
      (by linarith) (by linarith) hRB
  have hK : IsCompact K := by
    simpa only [K, Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : CubeShell.Ambient) (p / 2 - d / 2)
  have hKS : K ⊆ Q.source := closedCube_subset_source p hRB
  have hzero : (0 : CubeShell.Ambient) ∈ K := by
    change ‖(0 : CubeShell.Ambient)‖ ≤ p / 2 - d / 2
    simpa only [norm_zero] using hR.le
  have hsource : H.source = Q.source \ {0} := by
    rw [hHS, AddCircle.centeredCubeQuotient_source]
    ext x
    simp only [mem_ofPred_eq, mem_Ioo, mem_sdiff, mem_singleton_iff,
      norm_pos_iff, and_comm]
  have htarget : H.target ⊆ Q.source := by
    intro x hx
    rw [hHT] at hx
    rw [AddCircle.centeredCubeQuotient_source]
    exact hx.2
  have hfixed : EqOn H id (Q.source \ K) := by
    intro x hx
    apply hHfix
    have hxB : ‖x‖ < p / 2 := by
      simpa only [Q, AddCircle.centeredCubeQuotient_source, mem_ofPred_eq] using hx.1
    have hxR : p / 2 - d / 2 < ‖x‖ := lt_of_not_ge hx.2
    exact ⟨hxR.le, hxB.le⟩
  have himage : Q '' H.target ⊆ crossingBands p d := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hHT] at hx
    exact (centeredCubeQuotient_mem_crossingBands_iff p hd hdhalf hx.2).mpr hx.1
  have houtside : (Q '' K)ᶜ ⊆ crossingBands p d :=
    compl_centeredCubeImage_subset_crossingBands p hd hdhalf (by linarith)
  obtain ⟨C, hC, hCimage, hCchart, hCfix⟩ :=
    Q.exists_supported_chart_compression H hK hKS hzero hsource htarget hfixed himage houtside
  refine ⟨H, C, hHS, hHT, hHPL, hC, hCimage, hCchart, hCfix, ?_⟩
  exact hCfix.mono (crossingBands_subset_compl_centeredCubeImage p
    (by linarith : 0 < d / 2) (by linarith) le_rfl)

end TorusCube
