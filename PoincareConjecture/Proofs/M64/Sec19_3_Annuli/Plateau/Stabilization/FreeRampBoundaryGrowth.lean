import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampBoundaryComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryEnergyGrowth

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem auxiliaryCircle_free_ramp_boundary_power_growth
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
    ∃ width beta K : ℝ, 0 < width ∧ 0 < beta ∧ 0 ≤ K ∧
      (∀ x ∈ Icc (x0 - width) (x0 + width), width < x ∧ x + width < curvePeriod) ∧
      width < 1 ∧ ∀ x ∈ Icc (x0 - width) (x0 + width), ∀ r ∈ Ioc (0 : ℝ) width,
        A.annulus.boundaryDiskEnergy B x r ≤ K * r ^ beta ∧
          ∀ i : Fin 2, (∫ p in closedBall (annulusPoint x 0) r ∩ S,
            ‖A.annulus.column i p‖ ^ 2) ≤ K * r ^ beta := by
  obtain ⟨width, C0, hw, hC0, hwindow, hw1, hcomp⟩ :=
    auxiliaryCircle_free_ramp_boundary_angular_comparison P Q time gamma0 hgamma0 hramp0 q0
      he hei hread hRobs A hA hc1 hH0 hH1 hquot B hB hb hpos hmod hminimum hx0
  have hcomparison : ∀ x ∈ Icc (x0 - width) (x0 + width), ∀ epsilon R : ℝ,
      0 < epsilon → R ≤ width → ∀ᵐ r ∂volume.restrict (Icc epsilon R),
        A.annulus.boundaryDiskEnergy B x r ≤ C0 * A.annulus.boundaryAngularEnergy x r := by
    intro x hx epsilon R hepsilon hR
    exact hcomp x hx epsilon R hepsilon hR
  obtain ⟨beta, hbeta, K, hK, hpower⟩ := A.annulus.boundary_uniform_energy_power_growth B hB
    hei.isEmbedding hb hpos hC hcoercive hw hC0 hwindow hw1 hcomparison
  have hK0 : K ≤ (1 + 2 * C) * K := by nlinarith
  have hK1 : 2 * C * K ≤ (1 + 2 * C) * K := by nlinarith
  refine ⟨width, beta, (1 + 2 * C) * K, hw, hbeta, by positivity, hwindow, hw1, ?_⟩
  intro x hx r hr
  have hpow : 0 ≤ r ^ beta := Real.rpow_nonneg hr.1.le _
  refine ⟨(hpower x hx r hr).trans (mul_le_mul_of_nonneg_right hK0 hpow), ?_⟩
  intro i
  calc
    _ ≤ 2 * C * A.annulus.boundaryDiskEnergy B x r :=
      A.annulus.column_boundaryDisk_energy_le B hB hei.isEmbedding hb hpos hC hcoercive x r i
    _ ≤ 2 * C * (K * r ^ beta) :=
      mul_le_mul_of_nonneg_left (hpower x hx r hr) (by positivity)
    _ = (2 * C * K) * r ^ beta := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hK1 hpow

end PoincareConjecture.M64
