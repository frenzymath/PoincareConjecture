import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnularEnergyContraction
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyGrowthPower

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

namespace M64ObservedWeakAnnulus

theorem column_disk_energy_le
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {B : ℝ} (hb : ∀ q, ‖Q q‖ ≤ B) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (a : LoopPlane) (r : ℝ) (hball : Metric.ball a r ⊆ S) (i : Fin 2) :
    (∫ p in Metric.ball a r, ‖A.column i p‖ ^ 2) ≤ 2 * C * A.diskEnergy Q a r := by
  have hl := (Lp.memLp (A.column i)).mono_measure (Measure.restrict_mono hball le_rfl)
  have hi := (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mp hl
  have hEi := (A.energy_integrable Q hQ hei hb).mono_set hball
  unfold diskEnergy
  rw [← integral_const_mul]
  apply integral_mono_ae hi (hEi.const_mul _)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball (A.tangent i)] with p hp
  have hc := hcoercive (A.map p) (A.column i p) hp
  have h0 := mul_nonneg hC (hpos (A.map p) (A.column 0 p))
  have h1 := mul_nonneg hC (hpos (A.map p) (A.column 1 p))
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hc ⊢ <;> nlinarith

variable [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]

theorem uniform_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ W.energy Q)
    {R : ℝ} (hR : 0 < R) :
    ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ a : LoopPlane, Metric.closedBall a R ⊆ S →
        ∀ r ∈ Ioc (0 : ℝ) R, ∀ i : Fin 2,
          (∫ p in Metric.ball a r, ‖A.column i p‖ ^ 2) ≤ K * r ^ beta := by
  obtain ⟨q, hq, hq1, hstep⟩ :=
    A.energy_contraction g he hei hread Q hQ hpos hC hcoercive hmin
  obtain ⟨beta, hbeta, K, hK, hpower⟩ :=
    m64Morrey_exists_uniform_power_of_contraction hR hq hq1 (A.energy_nonneg Q hpos)
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  refine ⟨beta, hbeta, 2 * C * K, by positivity, ?_⟩
  intro a ha r hr i
  have hball (s : ℝ) (hs : s ≤ R) : Metric.ball a s ⊆ S :=
    Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall hs).trans ha)
  have hmono : MonotoneOn (A.diskEnergy Q a) (Ioc (0 : ℝ) R) := by
    intro s hs t ht hst
    exact A.diskEnergy_mono Q hQ hei.isEmbedding hb hpos a hst (hball t ht.2)
  have hbase := A.diskEnergy_le_energy Q hQ hei.isEmbedding hb hpos a R (hball R le_rfl)
  have hsmall := hpower (A.diskEnergy Q a) hmono hbase
    (fun s hs => hstep a s hs.1 ((Metric.closedBall_subset_closedBall hs.2).trans ha)) r hr
  calc
    _ ≤ 2 * C * A.diskEnergy Q a r :=
      A.column_disk_energy_le Q hQ hei.isEmbedding hb hpos hC hcoercive a r (hball r hr.2) i
    _ ≤ 2 * C * (K * r ^ beta) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by ring

theorem local_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ W.energy Q)
    (a : LoopPlane) (ha : a ∈ S) :
    ∃ rho : ℝ, 0 < rho ∧ Metric.closedBall a (2 * rho) ⊆ S ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∃ beta : ℝ, 0 < beta ∧
        ∀ b ∈ Metric.closedBall a rho, ∀ r ∈ Ioc (0 : ℝ) rho, ∀ i : Fin 2,
          (∫ p in Metric.ball b r, ‖A.column i p‖ ^ 2) ≤ K * r ^ beta := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  let rho := delta / 4
  have hrho : 0 < rho := div_pos hdelta (by norm_num)
  have hlarge : Metric.closedBall a (2 * rho) ⊆ S :=
    (Metric.closedBall_subset_ball (show 2 * rho < delta by dsimp [rho]; linarith)).trans hball
  obtain ⟨beta, hbeta, K, hK, hpower⟩ :=
    A.uniform_column_power_growth g he hei hread Q hQ hpos hC hcoercive hmin hrho
  refine ⟨rho, hrho, hlarge, K, hK, beta, hbeta, ?_⟩
  intro b hb r hr i
  have hba : Metric.closedBall b rho ⊆ S :=
    (Metric.closedBall_subset_closedBall' (show rho + dist b a ≤ 2 * rho from by
      linarith [Metric.mem_closedBall.mp hb])).trans hlarge
  exact hpower b hba r hr i

end M64ObservedWeakAnnulus

end PoincareConjecture
