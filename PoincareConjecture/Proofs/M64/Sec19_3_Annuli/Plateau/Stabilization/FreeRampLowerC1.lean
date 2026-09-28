import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampAllCenterGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.BoundaryRampRegularity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseRawConformality
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseObservedLaplacian
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeLowerBoundaryC1










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain





theorem auxiliaryCircle_free_ramp_lower_contMDiff_representative
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (q0 : Q.circle.Point)
    {e : Q.charts.Point → E}
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    {Robs : E →L[ℝ] LoopPlane}
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1) e Robs
      (auxiliaryCircleSection Q q0 ∘ gamma0) c1 H0 H1 (curvePeriod / circumference) degree)
    (hA : ContinuousOn A.annulus.map S) (hc1 : Continuous (e ∘ c1))
    (hp1 : Function.Periodic c1 curvePeriod)
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + degree)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + degree)
    (hquot : ∀ y, P.circle.quotient (H0 y) = (gamma0 y).2)
    (hdegree : angularPoint ((curvePeriod / circumference) * degree) = angularPoint 0)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point) (LC : LeviCivitaData g)
    (B : Q.charts.Point → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : Continuous B) {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hsymm : ∀ q v w, B q v w = B q w v) (hpos : ∀ q v, 0 ≤ B q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : Q.charts.Point) (v : E),
      v ∈ range (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q) → ‖v‖ ^ 2 ≤ C * B q v v)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    {modulus : ℝ} (hmod : 0 < modulus)
    (hminimum : ∀ s : ℝ, 0 < s →
      ∀ W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1) e Robs
          (auxiliaryCircleSection Q q0 ∘ gamma0) c1 H0 H1 (curvePeriod / circumference) degree,
        A.annulus.weightedEnergy B modulus ≤ W.annulus.weightedEnergy B s)
    {x0 : ℝ} (hx0 : x0 ∈ Ioo (0 : ℝ) curvePeriod) :
    let Phi := m64SourceAffine (annulusPoint x0 0)
      (Real.sqrt modulus) (Real.sqrt_pos.mpr hmod).ne'
    ∃ r : ℝ, 0 < r ∧ ∃ U : LoopPlane → Q.charts.Point,
      ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 U
        (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) ∧
      EqOn U (A.annulus.map ∘ Phi) (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) ∧
      ∀ z ∈ closedBall (0 : LoopPlane) r, z 1 = 0 →
        U z = auxiliaryCircleSection Q q0
          (gamma0 (A.label0 (x0 + Real.sqrt modulus * z 0))) := by
  have hsm := auxiliaryCircle_free_phase_contMDiffOn P Q e (he.of_le (by simp))
    hei.isEmbedding hread Robs hRobs A g B hB hb hdiag hmod (hminimum modulus hmod) hA
  have hc0 : Continuous (e ∘ (auxiliaryCircleSection Q q0 ∘ gamma0)) :=
    he.continuous.comp ((auxiliaryCircle_section_contMDiff Q q0).continuous.comp
      hgamma0.continuous)
  have hp0' : Function.Periodic (auxiliaryCircleSection Q q0 ∘ gamma0) curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q q0) (hp0 x)
  have hconf := auxiliaryCircle_free_phase_raw_conformal P Q e (he.of_le (by simp)) hei
    hread Robs hRobs A hc0 hc1 hp0' hp1 hH0 hH1 hdegree g B hB hb hpos hdiag
    hmod hminimum hA
  obtain ⟨C0, hC0, hforcing⟩ := auxiliaryCircle_free_phase_observed_laplacian_growth
    P Q e he hei.isEmbedding hread Robs hRobs A g LC B hB hb hdiag hmod
    (hminimum modulus hmod) hA
  obtain ⟨rho, hrho, hsub, beta, hbeta, K, hK, henergy⟩ :=
    auxiliaryCircle_free_ramp_all_center_column_growth P Q time gamma0 hgamma0 hramp0 q0
      he hei hread hRobs A (hsm.of_le (by simp)) hc1 hH0 hH1 hquot
      B hB hb hpos hC hcoercive hmod (hminimum modulus hmod) hx0
  obtain ⟨hcurve, hregular⟩ := auxiliaryCircle_shifted_ramp_regular
    P Q time gamma0 hgamma0 hramp0 q0 (A.label0 x0)
  exact A.lower_boundary_contMDiff_representative he hei.isEmbedding hread hsm hc0 hc1
    hH0 hH1 hrho hcurve (hregular 0) hsub hK hbeta henergy
    g B hB hb hsymm hpos hC hcoercive hdiag hmod hconf hC0 hforcing

end PoincareConjecture.M64
