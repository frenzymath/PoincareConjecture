import PoincareConjecture.Proofs.M76.Mathlib.PuncturedThreeTorusCompression
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartCompressionPL

set_option autoImplicit false

open Set Geometry

namespace TorusCube

theorem exists_punctured_PL_immersion_of_bands
    (p : ℝ) [Fact (0 < p)] {d : ℝ} (hd : 0 < d) (hdhalf : d < p / 2)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ((AddCircle p × AddCircle p) × AddCircle p) → F)
    (hf : IsLocalHomeomorphOn f (crossingBands p d))
    (hfPL : ∀ a b c : ℝ,
      let T := ((AddCircle.openPartialHomeomorphCoe p a).prod
        (AddCircle.openPartialHomeomorphCoe p b)).prod (AddCircle.openPartialHomeomorphCoe p c)
      LocallyPiecewiseAffineOn (f ∘ T) (T.source ∩ T ⁻¹' crossingBands p d)) :
    let q := AddCircle.centeredCubeQuotient p 0
    ∃ g : ((AddCircle p × AddCircle p) × AddCircle p) → F,
      IsLocalHomeomorphOn g {q}ᶜ ∧ EqOn g f (crossingBands p (d / 2)) ∧
      ∀ a b c : ℝ,
        let T := ((AddCircle.openPartialHomeomorphCoe p a).prod
          (AddCircle.openPartialHomeomorphCoe p b)).prod (AddCircle.openPartialHomeomorphCoe p c)
        LocallyPiecewiseAffineOn (g ∘ T) (T.source ∩ T ⁻¹' {q}ᶜ) := by
  let Q := AddCircle.centeredCubeQuotient p
  let K := {x : CubeShell.Ambient | ‖x‖ ≤ p / 2 - d / 2}
  have hRB : p / 2 - d / 2 < p / 2 := by linarith
  have hK : IsCompact K := by
    simpa only [K, Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : CubeShell.Ambient) (p / 2 - d / 2)
  have hKS : K ⊆ Q.source := closedCube_subset_source p hRB
  obtain ⟨H, C, hHS, hHT, hHPL, hC, hCimage, hCchart, hCfix, hCcore⟩ :=
    exists_punctured_three_torus_compression p hd hdhalf
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
  have himage : Q '' H.target ⊆ crossingBands p d := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hHT] at hx
    exact (centeredCubeQuotient_mem_crossingBands_iff p hd hdhalf hx.2).mpr hx.1
  have houtside : (Q '' K)ᶜ ⊆ crossingBands p d :=
    compl_centeredCubeImage_subset_crossingBands p hd hdhalf (by linarith)
  have hFQ : LocallyPiecewiseAffineOn (f ∘ Q) (Q.source ∩ Q ⁻¹' crossingBands p d) :=
    AddCircle.locallyPiecewiseAffineOn_comp_centeredCubeQuotient p
      f (crossingBands p d) (hfPL 0 0 0)
  refine ⟨f ∘ C, hf.comp hC hCimage, ?_, ?_⟩
  · intro z hz
    exact congrArg f (hCcore hz)
  · intro a b c
    let T := ((AddCircle.openPartialHomeomorphCoe p a).prod
      (AddCircle.openPartialHomeomorphCoe p b)).prod (AddCircle.openPartialHomeomorphCoe p c)
    have hTQ : LocallyPiecewiseAffineOn (T.trans Q.symm) (T.trans Q.symm).source :=
      (mem_piecewiseAffineGroupoid_iff CubeShell.Ambient (T.trans Q.symm)).mp
        (AddCircle.centeredCubeQuotient_transition_mem_piecewiseAffineGroupoid p a b c) |>.1
    have hH : LocallyPiecewiseAffineOn H H.source :=
      (mem_piecewiseAffineGroupoid_iff CubeShell.Ambient H).mp hHPL |>.1
    exact Q.locallyPiecewiseAffineOn_comp_supported_compression H T hK hKS
      hsource htarget hH hTQ C hCchart hCfix himage houtside f hFQ (hfPL a b c)

end TorusCube
