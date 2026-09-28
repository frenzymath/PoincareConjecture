import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamContraction
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyGrowthPower

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusSeamDomain

theorem seam_column_disk_energy_le
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {B : ℝ} (hb : ∀ q, ‖Q q‖ ≤ B) (hpos : ∀ q w, 0 ≤ Q q w w)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (w : E), w ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖w‖ ^ 2 ≤ C * Q q w w)
    (a : LoopPlane) (r : ℝ) (hball : Metric.ball a r ⊆ O) (i : Fin 2) :
    (∫ p in Metric.ball a r, ‖m64AnnulusSeamExtend (A.column i : LoopPlane → E) p‖ ^ 2) ≤
      2 * C * A.seamDiskEnergy Q a r := by
  have hl := (A.seam_extension_memLp.2 i).mono_measure (Measure.restrict_mono hball le_rfl)
  have hi := (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mp hl
  have hEi := (A.seamEnergyDensity_integrable Q hQ hei hb).mono_set hball
  unfold seamDiskEnergy
  rw [← integral_const_mul]
  apply integral_mono_ae hi (hEi.const_mul _)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball (A.seam_extension_tangent i)] with p hp
  have hc := hcoercive (m64AnnulusSeamExtend A.map p)
    (m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) hp
  have h0 := mul_nonneg hC (hpos (m64AnnulusSeamExtend A.map p)
    (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p))
  have h1 := mul_nonneg hC (hpos (m64AnnulusSeamExtend A.map p)
    (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p))
  dsimp only [seamEnergyDensity]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hc ⊢ <;> nlinarith

variable [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]

theorem seam_uniform_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q w, 0 ≤ Q q w w)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (w : E), w ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖w‖ ^ 2 ≤ C * Q q w w)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q)
    {R : ℝ} (hR : 0 < R) (hwidth : 2 * R < curvePeriod) :
    ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ a : LoopPlane, Metric.closedBall a R ⊆ O →
        ∀ r ∈ Ioc (0 : ℝ) R, ∀ i : Fin 2,
          (∫ p in Metric.ball a r,
            ‖m64AnnulusSeamExtend (A.column i : LoopPlane → E) p‖ ^ 2) ≤ K * r ^ beta := by
  obtain ⟨q, hq, hq1, hstep⟩ :=
    A.seam_energy_contraction g he hei hread Q hQ hpos hC hcoercive hmin
  obtain ⟨beta, hbeta, K, hK, hpower⟩ := m64Morrey_exists_uniform_power_of_contraction
    hR hq hq1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (A.energy_nonneg Q hpos))
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  refine ⟨beta, hbeta, 2 * C * K, by positivity, ?_⟩
  intro a ha r hr i
  have hball (s : ℝ) (hs : s ≤ R) : Metric.ball a s ⊆ O :=
    Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall hs).trans ha)
  have hmono : MonotoneOn (A.seamDiskEnergy Q a) (Ioc (0 : ℝ) R) := by
    intro s hs t ht hst
    exact A.seamDiskEnergy_mono Q hQ hei.isEmbedding hb hpos a hst (hball t ht.2)
  have hbase := A.seamDiskEnergy_le_energy Q hQ hei.isEmbedding hb hpos a R (hball R le_rfl)
  have hsmall := hpower (A.seamDiskEnergy Q a) hmono hbase
    (fun s hs => hstep a s hs.1 (by linarith [hs.2])
      ((Metric.closedBall_subset_closedBall hs.2).trans ha)) r hr
  calc
    _ ≤ 2 * C * A.seamDiskEnergy Q a r :=
      A.seam_column_disk_energy_le Q hQ hei.isEmbedding hb hpos hC hcoercive a r (hball r hr.2) i
    _ ≤ 2 * C * (K * r ^ beta) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by ring

theorem seam_local_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q w, 0 ≤ Q q w w)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (w : E), w ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖w‖ ^ 2 ≤ C * Q q w w)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q)
    (a : LoopPlane) (ha : a ∈ O) :
    ∃ rho : ℝ, 0 < rho ∧ Metric.closedBall a (2 * rho) ⊆ O ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∃ beta : ℝ, 0 < beta ∧
        ∀ b ∈ Metric.closedBall a rho, ∀ r ∈ Ioc (0 : ℝ) rho, ∀ i : Fin 2,
          (∫ p in Metric.ball b r,
            ‖m64AnnulusSeamExtend (A.column i : LoopPlane → E) p‖ ^ 2) ≤ K * r ^ beta := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp m64AnnulusSeamDomain_isOpen a ha
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let rho := min (delta / 4) (curvePeriod / 4)
  have hrho : 0 < rho := lt_min (by positivity) (by positivity)
  have hrd : rho ≤ delta / 4 := min_le_left _ _
  have hrP : rho ≤ curvePeriod / 4 := min_le_right _ _
  have hwidth : 2 * rho < curvePeriod := by linarith
  have hlarge : Metric.closedBall a (2 * rho) ⊆ O :=
    (Metric.closedBall_subset_ball (show 2 * rho < delta by linarith)).trans hball
  obtain ⟨beta, hbeta, K, hK, hpower⟩ :=
    A.seam_uniform_column_power_growth g he hei hread Q hQ hpos hC hcoercive hmin hrho hwidth
  refine ⟨rho, hrho, hlarge, K, hK, beta, hbeta, ?_⟩
  intro b hb r hr i
  have hba : Metric.closedBall b rho ⊆ O :=
    (Metric.closedBall_subset_closedBall' (show rho + dist b a ≤ 2 * rho from by
      linarith [Metric.mem_closedBall.mp hb])).trans hlarge
  exact hpower b hba r hr i

end PoincareConjecture.M64ObservedWeakAnnulus
