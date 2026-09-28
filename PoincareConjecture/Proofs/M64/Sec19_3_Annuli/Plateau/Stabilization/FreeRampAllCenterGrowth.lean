import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampBoundaryGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryAllCenterGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.InteriorAngularContraction
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedSubsetEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseCircleComparison

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem auxiliaryCircle_free_ramp_all_center_column_growth
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hramp0 : M63IsRampAt P gamma0 time) (q0 : Q.circle.Point)
    {e : Q.charts.Point → E}
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    {Robs : E →L[ℝ] LoopPlane}
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1) e Robs
      (auxiliaryCircleSection Q q0 ∘ gamma0) c1 H0 H1 (curvePeriod / circumference) D)
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.annulus.map S)
    (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    (hquot : ∀ y, P.circle.quotient (H0 y) = (gamma0 y).2)
    (B : Q.charts.Point → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : Continuous B) {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hpos : ∀ q v, 0 ≤ B q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : Q.charts.Point) (v : E),
      v ∈ range (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q) → ‖v‖ ^ 2 ≤ C * B q v v)
    {modulus : ℝ} (hmod : 0 < modulus)
    (hminimum : ∀ W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1) e Robs
        (auxiliaryCircleSection Q q0 ∘ gamma0) c1 H0 H1 (curvePeriod / circumference) D,
      A.annulus.weightedEnergy B modulus ≤ W.annulus.weightedEnergy B modulus)
    {x0 : ℝ} (hx0 : x0 ∈ Ioo (0 : ℝ) curvePeriod) :
    ∃ rho : ℝ, 0 < rho ∧
      closedBall (annulusPoint x0 0) (2 * rho) ⊆ m64AnnulusLowerDomain ∧
      ∃ beta : ℝ, 0 < beta ∧ ∃ K : ℝ, 0 ≤ K ∧
        ∀ z ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
          (∫ p in closedBall z r ∩ S, ∑ i : Fin 2, ‖A.annulus.column i p‖ ^ 2) ≤
            K * r ^ beta := by
  obtain ⟨width, beta, K0, hw, hbeta, hK0, hwindow, hw1, hedge⟩ :=
    auxiliaryCircle_free_ramp_boundary_power_growth P Q time gamma0 hgamma0 hramp0 q0
      he hei hread hRobs A hA hc1 hH0 hH1 hquot B hB hb hpos hC hcoercive hmod hminimum hx0
  obtain ⟨C0, hC0, hcomp⟩ := auxiliaryCircle_free_phase_circle_energy_comparison P Q
    (he.of_le (by simp)) hei hread hRobs A (Q.flow.metric time) B hB hpos hmod hminimum
  obtain ⟨q, hq, hq1, hcontract⟩ := A.annulus.energy_contraction_of_angular_comparison B hB
    hei.isEmbedding hb hpos hC hcoercive hC0 hcomp
  let density := fun p => (B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) +
    B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2
  have hdisk (z : LoopPlane) (r : ℝ) : A.annulus.diskEnergy B z r =
      ∫ p in closedBall z r, density p :=
    setIntegral_congr_set (M60.haar_ball_ae_eq_closedBall volume z r)
  have hw0 := hwindow x0 ⟨by linarith, by linarith⟩
  obtain ⟨gamma, hgamma, K, hK, hpower⟩ := m64Boundary_all_center_power density
    (A.annulus.energy_integrable B hB hei.isEmbedding hb)
    (fun p => div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num))
    hw hw0.1 hw0.2 hw1 hbeta hK0 hq hq1
    (fun x hx r hr => (hedge x hx r hr).1)
    (fun z r hr hball => by simpa only [hdisk] using hcontract z r hr hball)
  refine ⟨width / 8, by positivity, ?_, gamma, hgamma, 2 * C * K, by positivity, ?_⟩
  · exact (closedBall_subset_closedBall (by linarith : 2 * (width / 8) ≤ width / 2)).trans
      (m64Boundary_window_closedBall hw hw0.1 hw0.2 hw1)
  · intro z hz r hr
    calc
      _ ≤ 2 * C * ∫ p in closedBall z r ∩ S, density p :=
        A.annulus.column_sum_energy_le_on B hB hei.isEmbedding hb hcoercive inter_subset_right
      _ ≤ 2 * C * (K * r ^ gamma) :=
        mul_le_mul_of_nonneg_left (hpower z hz r hr) (by positivity)
      _ = _ := by ring

end PoincareConjecture.M64
