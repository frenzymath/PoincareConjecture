import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Core.Coordinates

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem retainedBand_mem_patch {p : S2} (hp : p ∈ retainedBand) :
    (p : E3) ∈ bandPatch 1 '' bandRectangle ∪ bandPatch (-1) '' bandRectangle := by
  have hz := retainedBand_latitude hp
  have hn : ((p : E3) 0)^2+((p : E3) 1)^2+((p : E3) 2)^2=1 := by
    have hn := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
    exact hn.symm
  have hh : 1 ≤ height p ∧ height p ≤ 13 / 10 := hp
  rw [height_apply] at hh
  have hsq : 0 ≤ 1-((p : E3) 2)^2 := by
    nlinarith [sq_nonneg ((p : E3) 0), sq_nonneg ((p : E3) 1)]
  have hs := Real.sq_sqrt hsq
  have hx : (p : E3) 0 ∈ Icc (bandLeft ((p : E3) 2)) (bandRight ((p : E3) 2)) := by
    dsimp [bandLeft, bandRight]
    constructor
    · apply max_le
      · dsimp [levelAbscissa]
        nlinarith [hh.1]
      · nlinarith [Real.sqrt_nonneg (1-((p : E3) 2)^2), sq_nonneg ((p : E3) 1)]
    · apply le_min
      · dsimp [upperAbscissa]
        nlinarith [hh.2]
      · nlinarith [Real.sqrt_nonneg (1-((p : E3) 2)^2), sq_nonneg ((p : E3) 1)]
  have hcont : ContinuousOn (bandX ((p : E3) 2)) (Icc 0 1) := by
    unfold bandX
    fun_prop
  have hx' : (p : E3) 0 ∈ Icc (bandX ((p : E3) 2) 0) (bandX ((p : E3) 2) 1) := by
    simpa [bandX] using hx
  obtain ⟨t, ht, hxt⟩ := intermediate_value_Icc (by norm_num : (0 : Real) ≤ 1) hcont hx'
  have hw : ((p : E3) 2, t) ∈ bandRectangle := ⟨hz, ht⟩
  have hrad : Real.sqrt (1-((p : E3) 2)^2-(bandX ((p : E3) 2) t)^2) = |(p : E3) 1| := by
    rw [hxt]
    rw [show 1-((p : E3) 2)^2-((p : E3) 0)^2 = ((p : E3) 1)^2 by nlinarith]
    exact Real.sqrt_sq_eq_abs _
  by_cases hy : 0 ≤ (p : E3) 1
  · left
    refine ⟨((p : E3) 2, t), hw, ?_⟩
    ext i
    fin_cases i
    · exact hxt
    · simp [bandPatch, hrad, abs_of_nonneg hy]
    · rfl
  · right
    refine ⟨((p : E3) 2, t), hw, ?_⟩
    ext i
    fin_cases i
    · exact hxt
    · simp [bandPatch, hrad, abs_of_neg (lt_of_not_ge hy)]
    · rfl

theorem retainedBand_image : (Subtype.val : S2 → E3) '' retainedBand =
    bandPatch 1 '' bandRectangle ∪ bandPatch (-1) '' bandRectangle := by
  apply Subset.antisymm
  · rintro q ⟨p, hp, rfl⟩
    exact retainedBand_mem_patch hp
  · rintro q (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact ⟨⟨bandPatch 1 w, bandPatch_mem_sphere (by norm_num) hw⟩,
        height_bandPatch (by norm_num) hw, rfl⟩
    · exact ⟨⟨bandPatch (-1) w, bandPatch_mem_sphere (by norm_num) hw⟩,
        height_bandPatch (by norm_num) hw, rfl⟩

theorem isConnected_retainedBand : IsConnected retainedBand := by
  have hr : IsConnected bandRectangle :=
    (isConnected_Icc (show lowerRoot ≤ (1 : Real) by linarith [lowerRoot_bounds.2])).prod
      (isConnected_Icc (by norm_num : (0 : Real) ≤ 1))
  have hw : ((1 : Real), (0 : Real)) ∈ bandRectangle :=
    ⟨⟨by linarith [lowerRoot_bounds.2], le_rfl⟩, ⟨le_rfl, by norm_num⟩⟩
  have heq : bandPatch (-1) (1, 0) = bandPatch 1 (1, 0) := by
    simp [bandPatch, bandX, bandLeft, levelAbscissa]
  have hc : IsConnected ((Subtype.val : S2 → E3) '' retainedBand) := by
    rw [retainedBand_image]
    exact (hr.image _ (bandPatch_continuous 1).continuousOn).union
      ⟨bandPatch 1 (1, 0), ⟨(1, 0), hw, rfl⟩, ⟨(1, 0), hw, heq⟩⟩
      (hr.image _ (bandPatch_continuous (-1)).continuousOn)
  exact ⟨hc.nonempty.of_image, Topology.IsInducing.subtypeVal.isPreconnected_image.mp hc.2⟩

theorem retainedBand_unique_critical_point :
    ∃ p ∈ retainedBand, mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ∧
      ∀ q ∈ retainedBand, mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0 ↔ q = p := by
  obtain ⟨p, hpz, hph, hpc, hu⟩ := exists_unique_critical_point_in_height_band
  refine ⟨p, ⟨hph.1.le, by linarith [hph.2]⟩, hpc, ?_⟩
  exact fun q hq => hu q hq

end Poincare.Manifold.Schoenflies.Saddle.Nested
