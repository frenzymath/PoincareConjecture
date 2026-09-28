import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialSmoothGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialColumnEnergyUpper
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakLocalEnergy







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
local notation "S" => interior m64AnnulusDomain
local notation "L" => m64AnnulusLowerStrip



theorem lowerDiskEnergy_eq_diskEnergy
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (a : LoopPlane) (r : ℝ)
    (hball : ball a r ⊆ S) : A.lowerDiskEnergy Q a r = A.diskEnergy Q a r := by
  apply setIntegral_congr_fun measurableSet_ball
  intro p hp
  simp only [lowerEnergyDensity, lowerExtensionMap, lowerExtensionColumn,
    m64AnnulusLowerExtend_right _ _ (hball hp)]



theorem lowerDiskEnergy_le_of_ball_subset
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {B : ℝ} (hB : ∀ q, ‖Q q‖ ≤ B) (hpos : ∀ q v, 0 ≤ Q q v v)
    {a b : LoopPlane} {r R : ℝ} (hsub : ball a r ⊆ ball b R)
    (hball : ball b R ⊆ O) : A.lowerDiskEnergy Q a r ≤ A.lowerDiskEnergy Q b R :=
  setIntegral_mono_set ((A.lower_energy_integrable hc0 Q hQ hei hB).mono_set hball)
    (Eventually.of_forall (A.lowerEnergyDensity_nonneg Q hpos))
    (Eventually.of_forall hsub)



theorem lower_smooth_energy_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {B : ℝ} (hB : ∀ q, ‖Q q‖ ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a : LoopPlane) (r : ℝ), 0 < r → ball a r ⊆ L →
      A.lowerDiskEnergy Q a r ≤ D * r ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := A.lower_extension_column_bound he hc0 hc0P
  have hB0 : 0 ≤ B := (norm_nonneg (Q (A.lowerExtensionMap 0))).trans (hB _)
  refine ⟨Real.pi * B * D ^ 2, by positivity, ?_⟩
  intro a r hr hball
  have hballO := hball.trans m64AnnulusLower_strip_subset
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hcol (i : Fin 2) :
      (∫ p in ball a r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤
        r ^ 2 * Real.pi * D ^ 2 := by
    have hl := ((A.lower_extension_memLp hce).2 i).mono_measure
      (Measure.restrict_mono hballO le_rfl)
    have hi := (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mp hl
    calc
      _ ≤ ∫ _ in ball a r, D ^ 2 := by
        apply integral_mono_ae hi integrableOn_const
        filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
        apply (sq_le_sq₀ (norm_nonneg _) hD).mpr
        exact hbound p (hballO hp) ((m64AnnulusLowerStrip_coordinates p).mp (hball hp)).2.2.2 i
      _ = _ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, EuclideanSpace.volume_ball_fin_two]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
          ENNReal.toReal_ofReal Real.pi_pos.le]
  have hupper := A.lower_disk_energy_le_column_bound he hc0 Q hQ hei hB a r hballO
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (hcol 0) (hcol 1))
    (div_nonneg hB0 (by norm_num : (0 : ℝ) ≤ 2))
  exact hupper.trans (hsum.trans_eq (by ring))

end PoincareConjecture.M64ObservedWeakAnnulus
