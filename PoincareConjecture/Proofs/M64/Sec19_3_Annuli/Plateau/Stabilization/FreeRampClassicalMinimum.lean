import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampClosedC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampSmoothMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeClassicalCompletion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ClosedC1BoundaryLabels
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ClosedStripBoundaryLabels
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ClassicalCompletionConformality
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicClassicalRegularity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryTransport






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain





theorem auxiliaryCircle_free_ramp_classical_minimum
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
    ∃ r : ℝ, 0 < r ∧ ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
      ∃ A : M64Annulus (Q.flow.metric time) (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
        ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.map
          {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1} ∧
        ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.map
          {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1} ∧
        ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
        A.area = m64LeastAnnulusArea (Q.flow.metric time) c0 c1 ∧
        ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
          r * m60AreaGram (Q.flow.metric time) A.map p 0 0 =
            r⁻¹ * m60AreaGram (Q.flow.metric time) A.map p 1 1 ∧
          m60AreaGram (Q.flow.metric time) A.map p 0 1 = 0 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
  let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
  let g := Q.flow.metric time
  obtain ⟨m, e, R, T, H0, H1, degree, B, he, hei, hread, hR, -, -, hH0, hH1,
      hquot0, hquot1, hB, hpos, hsymm, hdiag, r, hr, L, hL, harea, hminimum⟩ :=
    auxiliaryCircle_free_ramp_smooth_minimum P Q time gamma0 gamma1 hgamma0 hgamma1
      hp0 hp1 hramp0 hramp1 A0 hdelta hsmall
  have he1 : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨C, hC, hcoercive⟩ := m64ObservedMetric_coercivity_of_diagonal g e he1 B hdiag
  have hbounded : Bornology.IsBounded (range B) := (isCompact_range hB).isBounded
  obtain ⟨bound, hbound⟩ := hbounded.exists_norm_le
  have hb : ∀ q, ‖B q‖ ≤ bound := fun q => hbound _ (mem_range_self q)
  obtain ⟨U, hU, hUL, hseam, hU0, hU1⟩ :=
    auxiliaryCircle_free_ramp_closed_contMDiffOn P Q time gamma0 gamma1 hgamma0 hgamma1
      hp0 hp1 hramp0 hramp1 (Q.circle.quotient 0) (Q.circle.quotient delta)
      he hei hread hR L hL.continuousOn hH0 hH1 hquot0 hquot1 g (Q.flow.connection time)
      B hB hb hsymm hpos hC hcoercive hdiag hr hminimum
  have hp0' : Function.Periodic c0 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient 0)) (hp0 x)
  have hp1' : Function.Periodic c1 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient delta)) (hp1 x)
  have hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 2 c0 ∧
      ∀ x, curveVelocity (n := (n + 1) + 1) c0 x ≠ 0 := by
    have heq : (fun s => auxiliaryCircleSection Q (Q.circle.quotient 0)
        (gamma0 (s + 0))) = c0 := by
      funext s
      simp only [c0, Function.comp_apply, add_zero]
    have h := auxiliaryCircle_shifted_ramp_regular P Q time gamma0 hgamma0 hramp0
      (Q.circle.quotient 0) 0
    rw [heq] at h
    exact h
  have hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 2 c1 ∧
      ∀ x, curveVelocity (n := (n + 1) + 1) c1 x ≠ 0 := by
    have heq : (fun s => auxiliaryCircleSection Q (Q.circle.quotient delta)
        (gamma1 (s + 0))) = c1 := by
      funext s
      simp only [c1, Function.comp_apply, add_zero]
    have h := auxiliaryCircle_shifted_ramp_regular P Q time gamma1 hgamma1 hramp1
      (Q.circle.quotient delta) 0
    rw [heq] at h
    exact h
  have hlab := L.labels_continuous hH0 hH1
  obtain ⟨sigma0, hsigma0⟩ := m64ClosedC1Trace_exists_degreeOneLift he hread
    (hc0.1.of_le (by norm_num)) hc0.2 hlab.1 L.label0_monotone L.label0_period hU
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hU0
  obtain ⟨sigma1, hsigma1⟩ := m64ClosedC1Trace_exists_degreeOneLift he hread
    (hc1.1.of_le (by norm_num)) hc1.2 hlab.2 L.label1_monotone L.label1_period hU
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hU1
  obtain ⟨A, hAc1, hAL, -⟩ :=
    L.exists_classical_completion g hp0' hp1' U hU hUL hseam hU0 hU1
  have hAsmooth : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.map S := hL.congr hAL
  obtain ⟨V, hV, hVae, -, -, hVi⟩ :=
    auxiliaryCircle_free_ramp_halfTurn_radial_contMDiffOn P Q time gamma0 gamma1 hgamma0
      hgamma1 hp0 hp1 hramp0 hramp1 (Q.circle.quotient 0) (Q.circle.quotient delta)
      he hei hread hR L hH0 hH1 hquot0 hquot1 g (Q.flow.connection time) B hB hb hsymm
      hpos hC hcoercive hdiag hr hminimum
  have hLA : L.annulus.map =ᵐ[volume.restrict S] A.map :=
    (ae_restrict_mem isOpen_interior.measurableSet).mono fun _ hp => (hAL hp).symm
  have hrot : L.annulus.map ∘ m64AnnulusHalfTurn =ᵐ[volume.restrict S]
      A.map ∘ m64AnnulusHalfTurn :=
    m64AnnulusHalfTurn_measurePreserving.quasiMeasurePreserving.ae hLA
  have hstrip := m64Annulus_periodic_classical_regularity A hAc1 hAsmooth hV hVi
    (hVae.trans hrot)
  have hlabel0 := m64ClosedStripTrace_label_contDiff he hread
    (hc0.1.of_le (by norm_num)) hc0.2 hlab.1 hstrip.1
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) A.lower_boundary
  have hlabel1 := m64ClosedStripTrace_label_contDiff he hread
    (hc1.1.of_le (by norm_num)) hc1.2 hlab.2 hstrip.1
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) A.upper_boundary
  have hdegree := circle_phase_period_of_periodic_lift P.circle (fun x => (gamma0 x).2)
    (fun x => congrArg Prod.snd (hp0 x)) H0 hH0 hquot0
  have hconf := auxiliaryCircle_free_phase_raw_conformal P Q e he1 hei hread R hR L
    (he.continuous.comp hc0.1.continuous) (he.continuous.comp hc1.1.continuous)
    hp0' hp1' hH0 hH1 hdegree g B hB hb hpos hdiag hr hminimum hL.continuousOn
  have henergy : A.area = L.annulus.weightedEnergy B r :=
    L.annulus.area_eq_of_conformal_completion A he1 B hdiag hAL
      (hAc1.mono interior_subset) hr hconf
  have htransport := m64FreeBoundaryAreaTransport_of_collars hc0.1.continuous hp0'
    (m64PeriodicC1Curve_metric_lipschitz g (hc0.1.of_le (by norm_num)) hp0')
    hc1.1.continuous hp1'
    (m64PeriodicC1Curve_metric_lipschitz g (hc1.1.of_le (by norm_num)) hp1')
  have hfixed : ∃ D : M64Annulus g c0 c1, D.area = A.area := by
    have h := htransport sigma0 sigma1
    rw [hsigma0, hsigma1] at h
    exact h A
  obtain ⟨D, hD⟩ := hfixed
  have hleast : A.area = m64LeastAnnulusArea g c0 c1 := le_antisymm
    (henergy.trans_le harea) ((m64LeastAnnulusArea_le_annulus D).trans_eq hD)
  refine ⟨r, hr, sigma0, sigma1, ?_⟩
  rw [hsigma0, hsigma1]
  exact ⟨A, hstrip.1, hstrip.2, hlabel0, hlabel1, hleast,
    m64Annulus_conformal_of_interior_completion g hAL hconf⟩

end PoincareConjecture.M64
