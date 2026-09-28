import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreePhaseGlobalMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.NormalizedPhaseSeed
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.RampPhaseDegree
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ConfinedApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_free_ramp_weak_minimum
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (A0 : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta < auxiliary) :
    let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
    let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
    ∃ (m : ℕ) (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
      (R T : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
      (H0 H1 : ℝ ≃o ℝ) (D : ℝ)
      (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ),
      ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := (n + 1) + 1) e ∧
      (∀ q, R (e q) = planarCircleObservation q.1.2) ∧
      (∀ q, T (e q) = planarCircleObservation q.2) ∧
      0 < D ∧
      (∀ x, H0 (x + curvePeriod) = H0 x + D) ∧
      (∀ x, H1 (x + curvePeriod) = H1 x + D) ∧
      (∀ x, P.circle.quotient (H0 x) = (gamma0 x).2) ∧
      (∀ x, P.circle.quotient (H1 x) = (gamma1 x).2) ∧
      Continuous B ∧ (∀ q v, 0 ≤ B q v v) ∧
      (∀ q v w, B q v w = B q w v) ∧
      (∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
        B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
          (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = (Q.flow.metric time).inner q v v) ∧
      ∃ r : ℝ, 0 < r ∧
        ∃ L : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
            e R c0 c1 H0 H1 (curvePeriod / circumference) D,
          L.annulus.weightedEnergy B r ≤ m64LeastAnnulusArea (Q.flow.metric time) c0 c1 ∧
          ∀ s : ℝ, 0 < s →
            ∀ A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
                e R c0 c1 H0 H1 (curvePeriod / circumference) D,
              L.annulus.weightedEnergy B r ≤ A.annulus.weightedEnergy B s := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
  let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
  have hc0 : Continuous c0 :=
    (auxiliaryCircle_section_contMDiff Q _).continuous.comp hgamma0.continuous
  have hc1 : Continuous c1 :=
    (auxiliaryCircle_section_contMDiff Q _).continuous.comp hgamma1.continuous
  have hperiod0 : Function.Periodic c0 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient 0)) (hp0 x)
  have hperiod1 : Function.Periodic c1 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient delta)) (hp1 x)
  have hsub : interior m64AnnulusDomain ⊆
      preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1) := by
    intro p hp
    exact ((m64AnnulusInterior_coordinates p).mp hp).2.2
  obtain ⟨lo, hi, hlo, -, happrox⟩ := auxiliaryCircle_free_approximation_confined P Q time
    gamma0 gamma1 hgamma0 hgamma1 hp0 hp1 hramp0 A0 hdelta hsmall
  obtain ⟨r0, -, sigma0, sigma1, -, -, -, -, -, -, A, hA, -, -⟩ := happrox 1 one_pos
  obtain ⟨H0, H1, D, hD, hH0, hH1, hzero, hone⟩ := auxiliaryCircle_ramp_phase_data
    P Q time gamma0 gamma1 hgamma0 hgamma1 hp0 hp1 hramp0 hramp1
    (Q.circle.quotient 0) (Q.circle.quotient delta) sigma0 sigma1 A (hA.mono hsub)
  obtain ⟨m, e, R, T, he, hei, hread, hR, hT⟩ :=
    auxiliaryCircle_observation_with_two_circles P Q
  have he1 : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨B, K, hB, hK, hb, hpos, hsymm, hgram⟩ :=
    m64ChartReadable_observed_metric (Q.flow.metric time) e he1 hread
  have hdiag := m64ObservedMetric_tangent_diagonal (Q.flow.metric time) e he1 B hgram
  obtain ⟨C, hC, hcoercive⟩ :=
    m64ObservedMetric_tangent_coercivity (Q.flow.metric time) e he1 B hgram
  obtain ⟨W, -, -⟩ := auxiliaryCircle_normalized_freeWeakPhase_seed P Q time
    e he1 R hR c0 c1 hperiod0 hperiod1 H0 H1 hzero hone hH0 B hdiag
    sigma0 sigma1 A (hA.mono hsub)
  have hq : Q.circle.quotient 0 ≠ Q.circle.quotient delta := by
    intro hh
    have hz : (delta : AddCircle auxiliary) = 0 := hh.symm
    exact hdelta.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hdelta.le, hsmall⟩).mp hz)
  obtain ⟨V, v0, v1, hv, hv0, hv1⟩ := auxiliaryCircle_exists_separating_reader P Q e T hT hq
  have hfreq : curvePeriod / circumference ≠ 0 := by
    exact (div_pos (by unfold curvePeriod; positivity) P.circle.positive).ne'
  obtain ⟨r, hr, L, hminimum⟩ := M64FreeWeakPhaseAnnulus.weightedEnergy_attained_positive
    e he1 hei hread R c0 c1 hc0 hc1 H0 H1 hfreq hD.ne' hH0 hH1 V hv
    (fun x => hv0 (gamma0 x)) (fun x => hv1 (gamma1 x))
    B hB hK hb hpos hsymm hC hcoercive W
  refine ⟨m, e, R, T, H0, H1, D, B, he, hei, hread, hR, hT, hD, hH0, hH1,
    hzero, hone, hB, hpos, hsymm, hdiag, r, hr, L, ?_, hminimum⟩
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨s, hs, tau0, tau1, -, -, -, -, -, -, Aeps, hAeps, -, hEeps⟩ :=
    happrox eps heps
  obtain ⟨Weps, -, hWeps⟩ := auxiliaryCircle_normalized_freeWeakPhase_seed P Q time
    e he1 R hR c0 c1 hperiod0 hperiod1 H0 H1 hzero hone hH0 B hdiag
    tau0 tau1 Aeps (hAeps.mono hsub)
  exact (hminimum s (hlo.trans_le hs.1) Weps).trans ((hWeps s).trans_le hEeps.le)

end PoincareConjecture.M64
