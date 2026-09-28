import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusCircleComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakMinimizerPowerGrowth

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem weighted_energy_contraction
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v) {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ W.weightedEnergy Q modulus) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ (a : LoopPlane) (rho : ℝ), 0 < rho →
      Metric.closedBall a rho ⊆ S →
      A.diskEnergy Q a (rho * Real.exp (-1)) ≤ q * A.diskEnergy Q a rho := by
  obtain ⟨C0, hC0, hcomp⟩ :=
    A.weighted_circle_energy_comparison g he hei hread Q hQ hpos hmodulus hmin
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (q : M) : ‖Q q‖ ≤ B := hB _ (mem_range_self q)
  let L := C0 * (4 * C)
  have hL : 0 ≤ L := mul_nonneg hC0.le (mul_nonneg (by norm_num) hC)
  have hL2 : 0 < L + 2 := by linarith
  refine ⟨(L + 1) / (L + 2), div_pos (by linarith) hL2,
    (div_lt_one hL2).mpr (by linarith), ?_⟩
  intro a rho hrho hKS
  let Y := A.diskEnergy Q a (rho * Real.exp (-1))
  let X := A.diskEnergy Q a rho
  have hball : Metric.ball a rho ⊆ S := Metric.ball_subset_closedBall.trans hKS
  have hYX : Y ≤ X := A.diskEnergy_mono Q hQ hei.isEmbedding hb hpos a
    (mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by norm_num))) hball
  have hYpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      Y ≤ C0 * A.angularEnergy a rho s := by
    filter_upwards [hcomp a rho hrho hKS, ae_restrict_mem measurableSet_Icc] with s hs hsI
    have hsmall : rho * Real.exp (-1) ≤ rho * Real.exp (-s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsI.2])) hrho.le
    have hlarge : rho * Real.exp (-s) ≤ rho :=
      mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hsI.1))
    exact (A.diskEnergy_mono Q hQ hei.isEmbedding hb hpos a hsmall
      ((Metric.ball_subset_ball hlarge).trans hball)).trans hs
  have hYint : Y ≤ C0 * ∫ s in Icc (0 : ℝ) 1, A.angularEnergy a rho s := by
    have hi := integral_mono_ae (integrable_const Y)
      ((A.angularEnergy_integrable a hrho hKS).const_mul C0) hYpoint
    rw [integral_const_mul] at hi
    simpa using hi
  have hangular := A.angularEnergy_integral_le_annular_energy
    Q hQ hei.isEmbedding hb hpos hC hcoercive a hrho hKS
  have hY : Y ≤ L * (X - Y) :=
    hYint.trans ((mul_le_mul_of_nonneg_left hangular hC0.le).trans_eq (by dsimp [L, X, Y]; ring))
  change Y ≤ (L + 1) / (L + 2) * X
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hL2).mpr
  nlinarith

theorem weighted_uniform_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v) {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ W.weightedEnergy Q modulus) {R : ℝ} (hR : 0 < R) :
    ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ a : LoopPlane, Metric.closedBall a R ⊆ S →
        ∀ r ∈ Ioc (0 : ℝ) R, ∀ i : Fin 2,
          (∫ p in Metric.ball a r, ‖A.column i p‖ ^ 2) ≤ K * r ^ beta := by
  obtain ⟨q, hq, hq1, hstep⟩ :=
    A.weighted_energy_contraction g he hei hread Q hQ hpos hC hcoercive hmodulus hmin
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

theorem weighted_local_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v) {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ W.weightedEnergy Q modulus)
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
  obtain ⟨beta, hbeta, K, hK, hpower⟩ := A.weighted_uniform_column_power_growth
    g he hei hread Q hQ hpos hC hcoercive hmodulus hmin hrho
  refine ⟨rho, hrho, hlarge, K, hK, beta, hbeta, ?_⟩
  intro b hb r hr i
  have hba : Metric.closedBall b rho ⊆ S :=
    (Metric.closedBall_subset_closedBall' (show rho + dist b a ≤ 2 * rho from by
      linarith [Metric.mem_closedBall.mp hb])).trans hlarge
  exact hpower b hba r hr i

end PoincareConjecture.M64ObservedWeakAnnulus
