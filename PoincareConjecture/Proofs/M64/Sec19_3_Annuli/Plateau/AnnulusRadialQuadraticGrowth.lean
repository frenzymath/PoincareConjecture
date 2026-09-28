import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialSmoothGrowth







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain
local notation "L" => m64AnnulusLowerStrip



theorem lower_column_quadratic_of_ball_subset
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod)
    {a : LoopPlane} {r : ℝ} (hr : 0 < r) (hball : ball a r ⊆ L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ i : Fin 2,
      (∫ p in ball a r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤
        D * r ^ 2 := by
  obtain ⟨D0, hD0, hbound⟩ := A.lower_extension_column_bound he hc0 hc0P
  refine ⟨Real.pi * D0 ^ 2, by positivity, ?_⟩
  intro i
  have hballO : ball a r ⊆ O := hball.trans m64AnnulusLower_strip_subset
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hl := ((A.lower_extension_memLp hce).2 i).mono_measure
    (Measure.restrict_mono hballO le_rfl)
  have hi := (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mp hl
  calc
    _ ≤ ∫ _ in ball a r, D0 ^ 2 := by
      apply integral_mono_ae hi integrableOn_const
      filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
      have hpL := hball hp
      exact (sq_le_sq₀ (norm_nonneg _) hD0).mpr (hbound p
        (m64AnnulusLower_strip_subset hpL)
        ((m64AnnulusLowerStrip_coordinates p).mp hpL).2.2.2 i)
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, EuclideanSpace.volume_ball_fin_two]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal Real.pi_pos.le]
      ring

end PoincareConjecture.M64ObservedWeakAnnulus
