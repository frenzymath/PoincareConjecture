import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeHalfTurnRadialC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusTwoCutC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusCutTraces

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "T" => m64AnnulusHalfTurn

theorem auxiliaryCircle_free_ramp_closed_contMDiffOn
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
    ∃ U : LoopPlane → Q.charts.Point,
      ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 U m64AnnulusDomain ∧
      EqOn U A.annulus.map S ∧
      (∀ y ∈ Icc (0 : ℝ) 1,
        U (annulusPoint curvePeriod y) = U (annulusPoint 0 y)) ∧
      (∀ x ∈ Icc (0 : ℝ) curvePeriod,
        U (annulusPoint x 0) = auxiliaryCircleSection Q q0 (gamma0 (A.label0 x))) ∧
      ∀ x ∈ Icc (0 : ℝ) curvePeriod,
        U (annulusPoint x 1) = auxiliaryCircleSection Q q1 (gamma1 (A.label1 x)) := by
  let c0 := (auxiliaryCircleSection Q q0 ∘ gamma0) ∘ A.label0
  let c1 := (auxiliaryCircleSection Q q1 ∘ gamma1) ∘ A.label1
  let f := m64AnnulusRadialCompletion A.annulus.map c0 c1
  have hf := auxiliaryCircle_free_ramp_radial_contMDiffOn P Q time gamma0 gamma1
    hgamma0 hgamma1 hp0 hp1 hramp0 hramp1 q0 q1 he hei hread hRobs A hA hH0 hH1
    hquot0 hquot1 g LC B hB hb hsymm hpos hC hcoercive hdiag hmod hminimum
  obtain ⟨V, hV, hVae, hV0, hV1, -⟩ :=
    auxiliaryCircle_free_ramp_halfTurn_radial_contMDiffOn P Q time gamma0 gamma1
      hgamma0 hgamma1 hp0 hp1 hramp0 hramp1 q0 q1 he hei hread hRobs A hH0 hH1
      hquot0 hquot1 g LC B hB hb hsymm hpos hC hcoercive hdiag hmod hminimum
  have hfint : EqOn f A.annulus.map S := by
    intro p hp
    have hc := (m64AnnulusInterior_coordinates p).mp hp
    exact m64AnnulusRadialCompletion_interior _ _ _ ⟨hc.2.2.1, hc.2.2.2⟩
  have hfae : f =ᵐ[volume.restrict S] A.annulus.map :=
    (ae_restrict_mem isOpen_interior.measurableSet).mono fun _ hp => hfint hp
  have hrot : f ∘ T =ᵐ[volume.restrict S] A.annulus.map ∘ T :=
    m64AnnulusHalfTurn_measurePreserving.quasiMeasurePreserving.ae hfae
  have hVf : V =ᵐ[volume.restrict S] f ∘ T := hVae.trans hrot.symm
  have hleft := m64AnnulusHalfTurn_left_overlap hf.continuousOn hV.continuousOn hVf
  have hright := m64AnnulusHalfTurn_right_overlap hf.continuousOn hV.continuousOn hVf
  have hc0 : Function.Periodic c0 curvePeriod := by
    intro x
    change auxiliaryCircleSection Q q0 (gamma0 (A.label0 (x + curvePeriod))) =
      auxiliaryCircleSection Q q0 (gamma0 (A.label0 x))
    rw [A.label0_period, hp0]
  have hc1 : Function.Periodic c1 curvePeriod := by
    intro x
    change auxiliaryCircleSection Q q1 (gamma1 (A.label1 (x + curvePeriod))) =
      auxiliaryCircleSection Q q1 (gamma1 (A.label1 x))
    rw [A.label1_period, hp1]
  refine ⟨m64AnnulusCutCompletion f V,
    m64AnnulusCutCompletion_contMDiffOn hf hV hleft hright, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hc := (m64AnnulusInterior_coordinates p).mp hp
    exact (m64AnnulusCutCompletion_interior f V ⟨hc.1, hc.2.1⟩).trans (hfint hp)
  · intro y _
    exact (m64AnnulusCutCompletion_edges f V y).2.trans
      (m64AnnulusCutCompletion_edges f V y).1.symm
  · exact m64AnnulusCutCompletion_trace f V c0 hc0 0
      (m64AnnulusRadialCompletion_lower _ _ _) hV0
  · exact m64AnnulusCutCompletion_trace f V c1 hc1 1
      (m64AnnulusRadialCompletion_upper _ _ _) hV1

end PoincareConjecture.M64
