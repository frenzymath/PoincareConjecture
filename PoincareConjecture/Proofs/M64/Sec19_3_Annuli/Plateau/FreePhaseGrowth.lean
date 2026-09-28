import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseCircleComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakMinimizerPowerGrowth









set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain




theorem auxiliaryCircle_free_phase_column_power_growth
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    {e : Q.charts.Point → E}
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    {R : E →L[ℝ] LoopPlane} (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) D)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hpos : ∀ q v, 0 ≤ B q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : Q.charts.Point) (v : E),
      v ∈ range (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q) → ‖v‖ ^ 2 ≤ C * B q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hminimum : ∀ W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e R c0 c1 H0 H1 (curvePeriod / circumference) D,
      A.annulus.weightedEnergy B modulus ≤ W.annulus.weightedEnergy B modulus)
    (a : LoopPlane) (ha : a ∈ S) :
    ∃ rho : ℝ, 0 < rho ∧ closedBall a (2 * rho) ⊆ S ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∃ beta : ℝ, 0 < beta ∧
        ∀ b ∈ closedBall a rho, ∀ r ∈ Ioc (0 : ℝ) rho, ∀ i : Fin 2,
          (∫ p in ball b r, ‖A.annulus.column i p‖ ^ 2) ≤ K * r ^ beta := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  obtain ⟨C0, hC0, hcomp⟩ := auxiliaryCircle_free_phase_circle_energy_comparison
    P Q he hei hread hR A g B hB hpos hmodulus hminimum
  have hbounded : Bornology.IsBounded (range B) := (isCompact_range hB).isBounded
  obtain ⟨bound, hbound⟩ := hbounded.exists_norm_le
  have hb (q : Q.charts.Point) : ‖B q‖ ≤ bound := hbound _ (mem_range_self q)
  let L := C0 * (4 * C)
  have hL : 0 ≤ L := mul_nonneg hC0.le (mul_nonneg (by norm_num) hC)
  have hL2 : 0 < L + 2 := by linarith
  let q := (L + 1) / (L + 2)
  have hq : 0 < q := div_pos (by linarith) hL2
  have hq1 : q < 1 := (div_lt_one hL2).mpr (by linarith)
  have hstep (b : LoopPlane) (rho : ℝ) (hrho : 0 < rho) (hKS : closedBall b rho ⊆ S) :
      A.annulus.diskEnergy B b (rho * Real.exp (-1)) ≤ q * A.annulus.diskEnergy B b rho := by
    let Y := A.annulus.diskEnergy B b (rho * Real.exp (-1))
    let X := A.annulus.diskEnergy B b rho
    have hball : ball b rho ⊆ S := ball_subset_closedBall.trans hKS
    have hYX : Y ≤ X := A.annulus.diskEnergy_mono B hB hei.isEmbedding hb hpos b
      (mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by norm_num))) hball
    have hYpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
        Y ≤ C0 * A.annulus.angularEnergy b rho s := by
      filter_upwards [hcomp b rho hrho hKS, ae_restrict_mem measurableSet_Icc] with s hs hsI
      have hsmall : rho * Real.exp (-1) ≤ rho * Real.exp (-s) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hsI.2])) hrho.le
      have hlarge : rho * Real.exp (-s) ≤ rho :=
        mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hsI.1))
      exact (A.annulus.diskEnergy_mono B hB hei.isEmbedding hb hpos b hsmall
        ((ball_subset_ball hlarge).trans hball)).trans hs
    have hYint : Y ≤ C0 * ∫ s in Icc (0 : ℝ) 1, A.annulus.angularEnergy b rho s := by
      have hi := integral_mono_ae (integrable_const Y)
        ((A.annulus.angularEnergy_integrable b hrho hKS).const_mul C0) hYpoint
      rw [integral_const_mul] at hi
      simpa using hi
    have hangular := A.annulus.angularEnergy_integral_le_annular_energy
      B hB hei.isEmbedding hb hpos hC hcoercive b hrho hKS
    have hY : Y ≤ L * (X - Y) := hYint.trans
      ((mul_le_mul_of_nonneg_left hangular hC0.le).trans_eq (by dsimp [L, X, Y]; ring))
    change Y ≤ (L + 1) / (L + 2) * X
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hL2).mpr
    nlinarith
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  let rho := delta / 4
  have hrho : 0 < rho := div_pos hdelta (by norm_num)
  have hlarge : closedBall a (2 * rho) ⊆ S :=
    (closedBall_subset_ball (show 2 * rho < delta by dsimp [rho]; linarith)).trans hball
  obtain ⟨beta, hbeta, K, hK, hpower⟩ :=
    m64Morrey_exists_uniform_power_of_contraction hrho hq hq1 (A.annulus.energy_nonneg B hpos)
  refine ⟨rho, hrho, hlarge, 2 * C * K, by positivity, beta, hbeta, ?_⟩
  intro b hbmem r hr i
  have hba : closedBall b rho ⊆ S :=
    (closedBall_subset_closedBall' (show rho + dist b a ≤ 2 * rho from by
      linarith [mem_closedBall.mp hbmem])).trans hlarge
  have hball (s : ℝ) (hs : s ≤ rho) : ball b s ⊆ S :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hs).trans hba)
  have hmono : MonotoneOn (A.annulus.diskEnergy B b) (Ioc (0 : ℝ) rho) := by
    intro s hs t ht hst
    exact A.annulus.diskEnergy_mono B hB hei.isEmbedding hb hpos b hst (hball t ht.2)
  have hbase := A.annulus.diskEnergy_le_energy B hB hei.isEmbedding hb hpos b rho
    (hball rho le_rfl)
  have hsmall := hpower (A.annulus.diskEnergy B b) hmono hbase
    (fun s hs => hstep b s hs.1 ((closedBall_subset_closedBall hs.2).trans hba)) r hr
  calc
    _ ≤ 2 * C * A.annulus.diskEnergy B b r :=
      A.annulus.column_disk_energy_le B hB hei.isEmbedding hb hpos hC hcoercive b r
        (hball r hr.2) i
    _ ≤ 2 * C * (K * r ^ beta) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by ring

end PoincareConjecture.M64
