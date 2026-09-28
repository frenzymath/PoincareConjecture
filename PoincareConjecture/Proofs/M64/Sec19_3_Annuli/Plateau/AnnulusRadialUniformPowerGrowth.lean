import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialPowerGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyGrowthForcedUniform

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

theorem lower_column_disk_energy_le
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {B : ℝ} (hb : ∀ q, ‖Q q‖ ≤ B) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (a : LoopPlane) (r : ℝ) (hball : ball a r ⊆ O) (i : Fin 2) :
    (∫ p in ball a r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤
      2 * C * A.lowerDiskEnergy Q a r := by
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hl := ((A.lower_extension_memLp hce).2 i).mono_measure
    (Measure.restrict_mono hball le_rfl)
  have hi := (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mp hl
  have hEi := (A.lower_energy_integrable hce Q hQ hei hb).mono_set hball
  unfold lowerDiskEnergy
  rw [← integral_const_mul]
  apply integral_mono_ae hi (hEi.const_mul _)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball
    (A.lower_extension_tangent he hc0 i)] with p hp
  have hc := hcoercive (A.lowerExtensionMap p) (A.lowerExtensionColumn i p) hp
  have h0 := mul_nonneg hC (hpos (A.lowerExtensionMap p) (A.lowerExtensionColumn 0 p))
  have h1 := mul_nonneg hC (hpos (A.lowerExtensionMap p) (A.lowerExtensionColumn 1 p))
  dsimp only [lowerEnergyDensity]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hc ⊢ <;> nlinarith

variable [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]

theorem lower_uniform_energy_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0) (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q) :
    ∃ rho0 : ℝ, 0 < rho0 ∧ ∀ R ∈ Ioc (0 : ℝ) rho0,
      ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
        ∀ (a : LoopPlane), a 1 = 0 → closedBall a R ⊆ O →
          ∀ r ∈ Ioc (0 : ℝ) R, A.lowerDiskEnergy Q a r ≤ K * r ^ beta := by
  obtain ⟨rho0, hrho0, q, hq, hq1, D, hD, hcontract⟩ :=
    A.lower_energy_contraction g he hei hread hc0 hc0P Q hQ hpos hC hcoercive hmin
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  refine ⟨rho0, hrho0, ?_⟩
  intro R hR
  obtain ⟨beta, hbeta, K, hK, hpower⟩ :=
    m64Morrey_exists_uniform_power_of_forced_contraction hR.1 hq hq1
      (A.lowerTotalEnergy_nonneg Q hpos) hD
  refine ⟨beta, hbeta, K, hK, ?_⟩
  intro a ha hKO
  have hball (t : ℝ) (ht : t ≤ R) : ball a t ⊆ O :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall ht).trans hKO)
  apply hpower (A.lowerDiskEnergy Q a)
  · intro x hx y hy hxy
    exact A.lowerDiskEnergy_mono hce Q hQ hei.isEmbedding hb hpos a hxy (hball y hy.2)
  · exact fun r _ => A.lowerDiskEnergy_nonneg Q hpos a r
  · exact A.lowerDiskEnergy_le_total hce Q hQ hei.isEmbedding hb hpos a R (hball R le_rfl)
  · intro r hr
    exact hcontract a ha r hr.1 (hr.2.trans hR.2) ((closedBall_subset_closedBall hr.2).trans hKO)

theorem lower_uniform_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0) (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q) :
    ∃ rho0 : ℝ, 0 < rho0 ∧ ∀ R ∈ Ioc (0 : ℝ) rho0,
      ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
        ∀ (a : LoopPlane), a 1 = 0 → closedBall a R ⊆ O →
          ∀ r ∈ Ioc (0 : ℝ) R, ∀ i : Fin 2,
            (∫ p in ball a r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤ K * r ^ beta := by
  obtain ⟨rho0, hrho0, hpower⟩ :=
    A.lower_uniform_energy_power_growth g he hei hread hc0 hc0P Q hQ hpos hC hcoercive hmin
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  refine ⟨rho0, hrho0, ?_⟩
  intro R hR
  obtain ⟨beta, hbeta, K, hK, hpow⟩ := hpower R hR
  refine ⟨beta, hbeta, 2 * C * K, by positivity, ?_⟩
  intro a ha hKO r hr i
  calc
    _ ≤ 2 * C * A.lowerDiskEnergy Q a r :=
      A.lower_column_disk_energy_le he hc0 Q hQ hei.isEmbedding hb hpos hC hcoercive a r
        (ball_subset_closedBall.trans ((closedBall_subset_closedBall hr.2).trans hKO)) i
    _ ≤ 2 * C * (K * r ^ beta) := mul_le_mul_of_nonneg_left (hpow a ha hKO r hr) (by positivity)
    _ = _ := by ring

end PoincareConjecture.M64ObservedWeakAnnulus
