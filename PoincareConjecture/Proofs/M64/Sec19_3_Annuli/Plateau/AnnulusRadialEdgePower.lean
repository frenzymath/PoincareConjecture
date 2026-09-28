import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyGrowthForcedExponent
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialUniformPowerGrowth

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

theorem lower_edge_column_power
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.energy Q ≤ B.energy Q)
    {a : LoopPlane} (ha : a ∈ O) (ha0 : a 1 = 0) :
    ∃ R : ℝ, 0 < R ∧ closedBall a R ⊆ O ∧
      ∃ q : ℝ, 0 < q ∧ q < 1 ∧
        ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧ beta ≤ -Real.log q ∧
          ∀ r ∈ Ioc (0 : ℝ) R, ∀ i : Fin 2,
            (∫ p in ball a r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤ K * r ^ beta := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp
    m64AnnulusLowerDomain_isOpen a ha
  obtain ⟨rho0, hrho0, q, hq, hq1, D, hD, hcontract⟩ :=
    A.lower_energy_contraction g he hei hread hc0 hc0P Q hQ hpos hC hcoercive hmin
  let R := min (delta / 2) (rho0 / 2)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRdelta : R < delta := by
    dsimp [R]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hRO : closedBall a R ⊆ O := (closedBall_subset_ball hRdelta).trans hball
  have hRrho : R < rho0 := by
    dsimp [R]
    exact (min_le_right _ _).trans_lt (half_lt_self hrho0)
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  have hD0 : 0 ≤ A.lowerTotalEnergy Q := A.lowerTotalEnergy_nonneg Q hpos
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hmono : MonotoneOn (A.lowerDiskEnergy Q a) (Ioc (0 : ℝ) R) := by
    intro s hs t ht hst
    exact A.lowerDiskEnergy_mono hce Q hQ hei.isEmbedding hb hpos a hst
      (ball_subset_closedBall.trans ((closedBall_subset_closedBall ht.2).trans hRO))
  have hbase : A.lowerDiskEnergy Q a R ≤ A.lowerTotalEnergy Q :=
    A.lowerDiskEnergy_le_total hce Q hQ hei.isEmbedding hb hpos a R
      (ball_subset_closedBall.trans hRO)
  obtain ⟨beta, hbeta, K0, hK0, hbetaq, hpow⟩ :=
    m64Morrey_exists_uniform_power_of_forced_contraction_le hR hq hq1 hD0 hD
  have hpower := hpow (A.lowerDiskEnergy Q a) hmono
    (fun r hr => A.lowerDiskEnergy_nonneg Q hpos a r) hbase
    (fun r hr => hcontract a ha0 r hr.1 (hr.2.trans hRrho.le)
      ((closedBall_subset_closedBall hr.2).trans hRO))
  refine ⟨R, hR, hRO, q, hq, hq1, beta, hbeta, 2 * C * K0, by positivity, hbetaq, ?_⟩
  intro r hr i
  have hballr : ball a r ⊆ O := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall hr.2).trans hRO)
  calc
    _ ≤ 2 * C * A.lowerDiskEnergy Q a r :=
      A.lower_column_disk_energy_le he hc0 Q hQ hei.isEmbedding hb hpos hC hcoercive a r hballr i
    _ ≤ 2 * C * (K0 * r ^ beta) :=
      mul_le_mul_of_nonneg_left (hpower r hr) (by positivity)
    _ = _ := by ring

end PoincareConjecture.M64ObservedWeakAnnulus
