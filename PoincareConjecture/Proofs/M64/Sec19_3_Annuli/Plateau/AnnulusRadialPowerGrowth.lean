import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialContraction
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyGrowthForced







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain



theorem lower_energy_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0) (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q) :
    ∃ rho0 : ℝ, 0 < rho0 ∧
      ∀ (a : LoopPlane), a 1 = 0 → closedBall a rho0 ⊆ O →
        ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
          ∀ r ∈ Ioc (0 : ℝ) rho0,
            A.lowerDiskEnergy Q a r ≤ K * r ^ beta := by
  obtain ⟨rho0, hrho0, q, hq, hq1, D, hD, hcontract⟩ :=
    A.lower_energy_contraction g he hei hread hc0 hc0P Q hQ hpos hC hcoercive hmin
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  let D0 := A.lowerTotalEnergy Q
  have hD0 : 0 ≤ D0 := A.lowerTotalEnergy_nonneg Q hpos
  have hKdata (a : LoopPlane) (ha : a 1 = 0) (hKO : closedBall a rho0 ⊆ O) :
      ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
        ∀ r ∈ Ioc (0 : ℝ) rho0, A.lowerDiskEnergy Q a r ≤ K * r ^ beta := by
    let F := fun r => A.lowerDiskEnergy Q a r
    have hmono : MonotoneOn F (Ioc (0 : ℝ) rho0) := by
      intro x hx y hy hxy
      have hyKO : closedBall a y ⊆ O :=
        (closedBall_subset_closedBall hy.2).trans hKO
      exact A.lowerDiskEnergy_mono hce Q hQ hei.isEmbedding hb hpos a hxy
        (ball_subset_closedBall.trans hyKO)
    have hbase : F rho0 ≤ D0 := by
      exact A.lowerDiskEnergy_le_total hce Q hQ hei.isEmbedding hb hpos a rho0
        (ball_subset_closedBall.trans hKO)
    have hstep : ∀ r ∈ Ioc (0 : ℝ) rho0, F (r * Real.exp (-1)) ≤ q * F r + D * r ^ 2 := by
      intro r hr
      exact hcontract a ha r hr.1 hr.2 ((closedBall_subset_closedBall hr.2).trans hKO)
    obtain ⟨beta, hbeta, K, hK, hbound⟩ :=
      m64Morrey_energy_le_power_of_forced_contraction hrho0 hq hq1 hD0 hD hmono
        (fun r hr => A.lowerDiskEnergy_nonneg Q hpos a r) hbase hstep
    refine ⟨beta, hbeta, K, hK, ?_⟩
    intro r hr
    exact hbound r hr
  refine ⟨rho0, hrho0, ?_⟩
  intro a ha hKO
  exact hKdata a ha hKO

end PoincareConjecture.M64ObservedWeakAnnulus
