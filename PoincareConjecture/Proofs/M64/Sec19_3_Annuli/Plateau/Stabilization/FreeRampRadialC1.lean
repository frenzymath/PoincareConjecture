import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampUpperC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialC1










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





theorem auxiliaryCircle_free_ramp_radial_contMDiffOn
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (q0 q1 : Q.circle.Point) {e : Q.charts.Point → E}
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    {Robs : E →L[ℝ] LoopPlane}
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1) e Robs
      (auxiliaryCircleSection Q q0 ∘ gamma0) (auxiliaryCircleSection Q q1 ∘ gamma1)
      H0 H1 (curvePeriod / circumference) degree)
    (hA : ContinuousOn A.annulus.map S)
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + degree)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + degree)
    (hquot0 : ∀ y, P.circle.quotient (H0 y) = (gamma0 y).2)
    (hquot1 : ∀ y, P.circle.quotient (H1 y) = (gamma1 y).2)
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
          (auxiliaryCircleSection Q q0 ∘ gamma0) (auxiliaryCircleSection Q q1 ∘ gamma1)
          H0 H1 (curvePeriod / circumference) degree,
        A.annulus.weightedEnergy B modulus ≤ W.annulus.weightedEnergy B s) :
    ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1
      (m64AnnulusRadialCompletion A.annulus.map
        ((auxiliaryCircleSection Q q0 ∘ gamma0) ∘ A.label0)
        ((auxiliaryCircleSection Q q1 ∘ gamma1) ∘ A.label1))
      {p : LoopPlane | p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1} := by
  have hc0 : Continuous (e ∘ (auxiliaryCircleSection Q q0 ∘ gamma0)) :=
    he.continuous.comp ((auxiliaryCircle_section_contMDiff Q q0).continuous.comp
      hgamma0.continuous)
  have hc1 : Continuous (e ∘ (auxiliaryCircleSection Q q1 ∘ gamma1)) :=
    he.continuous.comp ((auxiliaryCircle_section_contMDiff Q q1).continuous.comp
      hgamma1.continuous)
  have hp0' : Function.Periodic (auxiliaryCircleSection Q q0 ∘ gamma0) curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q q0) (hp0 x)
  have hp1' : Function.Periodic (auxiliaryCircleSection Q q1 ∘ gamma1) curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q q1) (hp1 x)
  have hdegree := circle_phase_period_of_periodic_lift P.circle (fun x => (gamma0 x).2)
    (fun x => congrArg Prod.snd (hp0 x)) H0 hH0 hquot0
  have hsm := auxiliaryCircle_free_phase_contMDiffOn P Q e (he.of_le (by simp))
    hei.isEmbedding hread Robs hRobs A g B hB hb hdiag hmod (hminimum modulus hmod) hA
  apply m64AnnulusRadialCompletion_contMDiffOn _ _ _ (hsm.of_le (by simp))
  · intro x hx
    obtain ⟨r, hr, U, hU, heq, htrace⟩ :=
      auxiliaryCircle_free_ramp_lower_contMDiff_representative P Q time gamma0 hgamma0
        hp0 hramp0 q0 he hei hread hRobs A hA hc1 hp1' hH0 hH1 hquot0 hdegree
        g LC B hB hb hsymm hpos hC hcoercive hdiag hmod hminimum hx
    exact m64AnnulusRadialCompletion_lower_contMDiffWithinAt _ _ _ x
      (Real.sqrt_pos.mpr hmod) hr U hU heq htrace
  · intro x hx
    obtain ⟨r, hr, U, hU, heq, htrace⟩ :=
      auxiliaryCircle_free_ramp_upper_contMDiff_representative P Q time gamma1 hgamma1
        hp1 hramp1 q1 he hei hread hRobs A hA hc0 hp0' hH0 hH1 hquot1 hdegree
        g LC B hB hb hsymm hpos hC hcoercive hdiag hmod hminimum hx
    exact m64AnnulusRadialCompletion_upper_contMDiffWithinAt _ _ _ x
      (Real.sqrt_pos.mpr hmod) hr U hU heq htrace

end PoincareConjecture.M64
