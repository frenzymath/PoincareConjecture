import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampAllCenterGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeLowerHolder

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

theorem auxiliaryCircle_free_ramp_lower_holder
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
      ∃ beta : ℝ, 0 < beta ∧ ∃ H : ℝ, 0 ≤ H ∧ ∃ U : LoopPlane → Q.charts.Point,
        ContinuousOn U (ball (annulusPoint x0 0) rho) ∧
        EqOn U A.annulus.map (ball (annulusPoint x0 0) rho ∩ S) ∧
        (∀ x, annulusPoint x 0 ∈ ball (annulusPoint x0 0) rho →
          U (annulusPoint x 0) = auxiliaryCircleSection Q q0 (gamma0 (A.label0 x))) ∧
        ∀ x ∈ ball (annulusPoint x0 0) rho, ∀ y ∈ ball (annulusPoint x0 0) rho,
          dist (e (U x)) (e (U y)) ≤ H * (dist x y) ^ beta := by
  obtain ⟨rho, hrho, hsub, beta, hbeta, K, hK, henergy⟩ :=
    auxiliaryCircle_free_ramp_all_center_column_growth P Q time gamma0 hgamma0 hramp0 q0
      he hei hread hRobs A hA hc1 hH0 hH1 hquot B hB hb hpos hC hcoercive hmod hminimum hx0
  have hc0 : Continuous (e ∘ (auxiliaryCircleSection Q q0 ∘ gamma0)) :=
    he.continuous.comp ((auxiliaryCircle_section_contMDiff Q q0).continuous.comp
      hgamma0.continuous)
  obtain ⟨H, hH, U, hU, hUeq, htrace, hholder⟩ := A.lower_target_holder_representative
    (he.of_le (by simp)) hei hA hc0 hc1 hH0 hH1 hrho hsub hK hbeta henergy
  refine ⟨rho / 2, half_pos hrho, ?_, beta / 2, half_pos hbeta,
    H, hH, U, hU, hUeq, htrace, hholder⟩
  exact (closedBall_subset_closedBall (by linarith : 2 * (rho / 2) ≤ 2 * rho)).trans hsub

end PoincareConjecture.M64
