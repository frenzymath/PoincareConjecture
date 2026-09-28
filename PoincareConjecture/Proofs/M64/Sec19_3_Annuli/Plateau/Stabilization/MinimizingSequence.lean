import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ConfinedApproximation












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "Strip" => preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)



theorem auxiliaryCircle_free_minimizing_sequence
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp : M63IsRampAt P gamma0 time)
    (A0 : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta < auxiliary) :
    let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
    let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
      ∃ (r : ℕ → ℝ) (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
        (A : ∀ j, M64Annulus (Q.flow.metric time)
          (c0 ∘ (sigma0 j).map) (c1 ∘ (sigma1 j).map)),
        (∀ j, r j ∈ Icc lo hi) ∧
        (∀ j, ContDiff ℝ 1 (sigma0 j).map ∧ ContDiff ℝ 1 (sigma1 j).map) ∧
        (∀ j, StrictMono (sigma0 j).map ∧ StrictMono (sigma1 j).map) ∧
        (∀ j x, 0 < deriv (sigma0 j).map x ∧ 0 < deriv (sigma1 j).map x) ∧
        (∀ j, ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 (A j).map Strip) ∧
        (∀ j, m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) (r j) ≤
          m64LeastAnnulusArea (Q.flow.metric time) c0 c1 + 1) ∧
        Tendsto (fun j => m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) (r j))
          atTop (𝓝 (m64LeastAnnulusArea (Q.flow.metric time) c0 c1)) := by
  classical
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
  let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
  obtain ⟨lo, hi, hlo, hlohi, hcand⟩ := auxiliaryCircle_free_approximation_confined
    P Q time gamma0 gamma1 hgamma0 hgamma1 hp0 hp1 hramp A0 hdelta hsmall
  choose r hr sigma0 sigma1 hs0 hs1 hm0 hm1 hd0 hd1 A hA hI hE using
    fun j : ℕ => hcand (1 / ((j : ℝ) + 1)) (by positivity)
  have hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 1 c0 :=
    ((auxiliaryCircle_section_contMDiff Q _).of_le (by simp)).comp
      (hgamma0.of_le (by norm_num))
  have hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 1 c1 :=
    ((auxiliaryCircle_section_contMDiff Q _).of_le (by simp)).comp
      (hgamma1.of_le (by norm_num))
  have hperiod0 : Function.Periodic c0 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient 0)) (hp0 x)
  have hperiod1 : Function.Periodic c1 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient delta)) (hp1 x)
  have htransport := m64FreeBoundaryAreaTransport_of_collars hc0.continuous hperiod0
    (m64PeriodicC1Curve_metric_lipschitz (Q.flow.metric time) hc0 hperiod0)
    hc1.continuous hperiod1
    (m64PeriodicC1Curve_metric_lipschitz (Q.flow.metric time) hc1 hperiod1)
  have hlower (j : ℕ) : m64LeastAnnulusArea (Q.flow.metric time) c0 c1 ≤
      m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) (r j) :=
    m64LeastAnnulusArea_le_free_weightedGramEnergy htransport (sigma0 j) (sigma1 j)
      (A j) (hlo.trans_le (hr j).1) (hI j)
  have hbound (j : ℕ) : m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) (r j) ≤
      m64LeastAnnulusArea (Q.flow.metric time) c0 c1 + 1 := by
    have hsmallj : 1 / ((j : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : 0 < (j : ℝ) + 1)).mpr
        (by linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j])
    exact (hE j).le.trans (add_le_add le_rfl hsmallj)
  refine ⟨lo, hi, hlo, hlohi, r, sigma0, sigma1, A, hr, fun j => ⟨hs0 j, hs1 j⟩,
    fun j => ⟨hm0 j, hm1 j⟩, fun j x => ⟨hd0 j x, hd1 j x⟩, hA, hbound, ?_⟩
  have hlim : Tendsto
      (fun j : ℕ => m64LeastAnnulusArea (Q.flow.metric time) c0 c1 + 1 / ((j : ℝ) + 1))
      atTop (𝓝 (m64LeastAnnulusArea (Q.flow.metric time) c0 c1)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    hlower (fun j => (hE j).le)

end PoincareConjecture.M64
