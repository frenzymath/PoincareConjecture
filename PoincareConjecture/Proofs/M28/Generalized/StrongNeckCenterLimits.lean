import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCenterCharts
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.NormalChartFlowLimit











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

local notation "E" => EuclideanSpace ℝ (Fin 3)



def GeneralizedStrongNeck.rescaled_eighth_flow
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon)
    (H : RescaledRawCylinderData (C := F.slice t)
      (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
      (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S)) :
    RicciFlow 3 (strongNeckOpen S) (Icc (-(1 / 8 : ℝ)) 0) :=
  Poincare.Geometry.RicciFlow.Harnack.restrictFlow
    (GeneralizedStrongNeck.rescaled_half_flow S H)
    (fun _ hs => ⟨by linarith [hs.1], hs.2⟩) ordConnected_Icc
    ⟨-(1 / 8 : ℝ), by norm_num, 0, by norm_num, by norm_num⟩






theorem exists_strongNeck_source_center_limit_accuracy
    (hShi : LocalCurvatureDerivativeEstimates.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∃ K R rho : ℝ, ∃ hrho : 0 < rho,
        0 < K ∧ 0 < R ∧ R < 1 / 8 ∧ 2 * rho < R ∧
        ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
          ∀ (F : ℕ → GeneralizedRicciFlowData.{u}) (t : ℕ → ℝ)
            (S : ∀ i, GeneralizedStrongNeck (F i) (t i) epsilon)
            (H : ∀ i, RescaledRawCylinderData (C := (F i).slice (t i))
              (U := strongNeckOpen (S i)) (J := strongNeckBackwardInterval)
              (strongNeckCylinder (S i)) (GeneralizedStrongNeck.physical_interval_subset (S i))),
            ∃ Phi : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) E (strongNeckOpen (S i)) ∞,
              (∀ i, (Phi i).source = Metric.ball 0 R ∧
                (Phi i).target =
                  ((GeneralizedStrongNeck.rescaled_half_flow (S i) (H i)).metric 0).ball
                  (strongNeckSourceCenter (S i)) R ∧
                Phi i 0 = strongNeckSourceCenter (S i) ∧
                (∀ x ∈ Metric.ball 0 R,
                  ((GeneralizedStrongNeck.rescaled_half_flow (S i) (H i)).metric 0).edist
                    (strongNeckSourceCenter (S i)) (Phi i x) = ENNReal.ofReal ‖x‖) ∧
                (∀ v w, ((GeneralizedStrongNeck.rescaled_half_flow
                  (S i) (H i)).metric 0).pullbackCoefficients
                  (Phi i) 0 v w = inner ℝ v w) ∧
                (∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
                  (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤
                    ((GeneralizedStrongNeck.rescaled_half_flow
                      (S i) (H i)).metric 0).pullbackCoefficients
                      (Phi i) x v v ∧
                  ((GeneralizedStrongNeck.rescaled_half_flow
                    (S i) (H i)).metric 0).pullbackCoefficients
                    (Phi i) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
                ((GeneralizedStrongNeck.rescaled_half_flow
                  (S i) (H i)).connection 0).scalarCurvature
                  (Phi i 0) = 1) ∧
              (∀ i s, s ∈ Icc (-(1 / 8 : ℝ)) 0 → ∀ x : strongNeckOpen (S i),
                ((GeneralizedStrongNeck.rescaled_eighth_flow
                  (S i) (H i)).connection s).curvatureTensorNorm
                  x ≤ K) ∧
              (letI : Nonempty (Metric.ball (0 : E) rho) := ⟨⟨0, Metric.mem_ball_self hrho⟩⟩;
                Nonempty (FixedCoordinateFlowLimit
                  (fun i => GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i))
                  (Metric.ball 0 rho) Metric.isOpen_ball (fun i x => Phi i x))) := by
  classical
  obtain ⟨epsilon₀, hepsilon₀, hthreshold, K, R, rho, hK, _hRdef,
      hR, hRsmall, hrho, hrhoR, hfamily⟩ :=
    exists_strongNeck_source_center_charts_accuracy hShi
  refine ⟨epsilon₀, hepsilon₀, hthreshold, K, R, rho, hrho, hK, hR, hRsmall, hrhoR, ?_⟩
  intro epsilon hepsilon hsmall F t S H
  obtain ⟨B, hB, hsource⟩ := hfamily epsilon hepsilon hsmall
  have hex (i : ℕ) := hsource (F i) (t i) (S i) (H i)
  choose hcurv L Phi hdomain htarget hzero hL hderivative hnormal hgeo hspeed
    hdist hell hjets hscalar using hex
  refine ⟨Phi, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hdomain i, htarget i, hzero i, hdist i, hnormal i, hell i, hscalar i⟩
  · intro i s hs x
    exact hcurv i s ⟨by linarith [hs.1], hs.2⟩ x
  · exact exists_fixedCoordinateFlowLimit_of_normal_charts
      (by norm_num : (0 : ℝ) < 1 / 8) hrho hrhoR hK.le
      (fun i => GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i))
      (fun i => strongNeckSourceCenter (S i)) L Phi hdomain hzero hL hderivative hgeo hspeed
      hell (fun i s hs x => hcurv i s ⟨by linarith [hs.1], hs.2⟩ x)
      B (fun m => (hB m).le)
      (fun m i s hs x hx => hjets i m s ⟨by linarith [hs.1], hs.2⟩ x hx)

end PoincareConjecture.M28
