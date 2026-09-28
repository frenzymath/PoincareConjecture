import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampLowerC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseRadialFlip

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

theorem auxiliaryCircle_free_ramp_upper_contMDiff_representative
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma1 : ℝ → P.charts.Point)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp1 : M63IsRampAt P gamma1 time) (q1 : Q.circle.Point)
    {e : Q.charts.Point → E}
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    {Robs : E →L[ℝ] LoopPlane}
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c0 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1) e Robs
      c0 (auxiliaryCircleSection Q q1 ∘ gamma1) H0 H1 (curvePeriod / circumference) degree)
    (hA : ContinuousOn A.annulus.map S) (hc0 : Continuous (e ∘ c0))
    (hp0 : Function.Periodic c0 curvePeriod)
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + degree)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + degree)
    (hquot : ∀ y, P.circle.quotient (H1 y) = (gamma1 y).2)
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
          c0 (auxiliaryCircleSection Q q1 ∘ gamma1) H0 H1 (curvePeriod / circumference) degree,
        A.annulus.weightedEnergy B modulus ≤ W.annulus.weightedEnergy B s)
    {x0 : ℝ} (hx0 : x0 ∈ Ioo (0 : ℝ) curvePeriod) :
    let Phi := m64SourceAffine (annulusPoint x0 0)
      (Real.sqrt modulus) (Real.sqrt_pos.mpr hmod).ne'
    let Psi := m64AnnulusRadialFlip ∘ Phi
    ∃ r : ℝ, 0 < r ∧ ∃ U : LoopPlane → Q.charts.Point,
      ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 U
        (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) ∧
      EqOn U (A.annulus.map ∘ Psi) (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) ∧
      ∀ z ∈ closedBall (0 : LoopPlane) r, z 1 = 0 →
        U z = auxiliaryCircleSection Q q1
          (gamma1 (A.label1 (x0 + Real.sqrt modulus * z 0))) := by
  obtain ⟨W, hmap, hlabel, -, -, hminW⟩ :=
    A.exists_radial_flip_minimum hH0 hH1 B modulus hminimum
  have hW : ContinuousOn W.annulus.map S := by
    rw [hmap]
    apply hA.comp m64AnnulusRadialFlip.continuous.continuousOn
    intro p hp
    change p ∈ m64AnnulusRadialFlip ⁻¹' S
    rwa [m64AnnulusRadialFlip_preimage_interior]
  obtain ⟨r, hr, U, hU, heq, htrace⟩ :=
    auxiliaryCircle_free_ramp_lower_contMDiff_representative P Q time gamma1 hgamma1
      hp1 hramp1 q1 he hei hread hRobs W hW hc0 hp0 hH1 hH0 hquot hdegree
      g LC B hB hb hsymm hpos hC hcoercive hdiag hmod hminW hx0
  refine ⟨r, hr, U, hU, ?_, ?_⟩
  · simpa only [hmap, Function.comp_assoc] using heq
  · simpa only [hlabel] using htrace

end PoincareConjecture.M64
