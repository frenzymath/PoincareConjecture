import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeHalfTurnContinuousMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampRadialC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeRadialCompletion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseInteriorSmooth

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "T" => m64AnnulusHalfTurn

theorem auxiliaryCircle_free_ramp_halfTurn_radial_contMDiffOn
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
      ∀ Z : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1) e Robs
          (auxiliaryCircleSection Q q0 ∘ gamma0) (auxiliaryCircleSection Q q1 ∘ gamma1)
          H0 H1 (curvePeriod / circumference) degree,
        A.annulus.weightedEnergy B modulus ≤ Z.annulus.weightedEnergy B s) :
    ∃ U : LoopPlane → Q.charts.Point,
      ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 U
        {p : LoopPlane | p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1} ∧
      U =ᵐ[volume.restrict S] A.annulus.map ∘ T ∧
      (∀ x : ℝ, U (annulusPoint x 0) = auxiliaryCircleSection Q q0
        (gamma0 (A.label0 (x + curvePeriod / 2)))) ∧
      (∀ x : ℝ, U (annulusPoint x 1) = auxiliaryCircleSection Q q1
        (gamma1 (A.label1 (x + curvePeriod / 2)))) ∧
      ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ U S := by
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
  obtain ⟨W, hcont, hmap, hl0, hl1, -, -, hminW⟩ :=
    auxiliaryCircle_free_phase_halfTurn_continuous_minimum P Q (he.of_le (by simp)) hei
      hread hRobs A hc0 hc1 hp0' hp1' hH0 hH1 hdegree g B hB hb hpos hdiag hmod hminimum
  let U := m64AnnulusRadialCompletion W.annulus.map
    ((auxiliaryCircleSection Q q0 ∘ gamma0) ∘ W.label0)
    ((auxiliaryCircleSection Q q1 ∘ gamma1) ∘ W.label1)
  have hC1 :=
    auxiliaryCircle_free_ramp_radial_contMDiffOn P Q time gamma0 gamma1 hgamma0 hgamma1
      hp0 hp1 hramp0 hramp1 q0 q1 he hei hread hRobs W hcont hH0 hH1 hquot0 hquot1 g LC B
      hB hb hsymm hpos hC hcoercive hdiag hmod hminW
  have hWi := auxiliaryCircle_free_phase_contMDiffOn P Q e (he.of_le (by simp))
    hei.isEmbedding hread Robs hRobs W g B hB hb hdiag hmod (hminW modulus hmod) hcont
  refine ⟨U, hC1, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hmap, ae_restrict_mem isOpen_interior.measurableSet] with p hp hpS
    have hc := (m64AnnulusInterior_coordinates p).mp hpS
    exact (m64AnnulusRadialCompletion_interior _ _ _ ⟨hc.2.2.1, hc.2.2.2⟩).trans hp
  · intro x
    rw [show U (annulusPoint x 0) = auxiliaryCircleSection Q q0 (gamma0 (W.label0 x)) from
      m64AnnulusRadialCompletion_lower _ _ _ x, hl0]
    exact m64FreePhaseHalfTurnLabel_trace hp0' x
  · intro x
    rw [show U (annulusPoint x 1) = auxiliaryCircleSection Q q1 (gamma1 (W.label1 x)) from
      m64AnnulusRadialCompletion_upper _ _ _ x, hl1]
    exact m64FreePhaseHalfTurnLabel_trace hp1' x
  · apply hWi.congr
    intro p hp
    have hc := (m64AnnulusInterior_coordinates p).mp hp
    exact m64AnnulusRadialCompletion_interior _ _ _ ⟨hc.2.2.1, hc.2.2.2⟩

end PoincareConjecture.M64
