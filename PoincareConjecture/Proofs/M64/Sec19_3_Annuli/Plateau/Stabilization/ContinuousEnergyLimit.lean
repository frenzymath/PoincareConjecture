import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.LabelLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RampContinuousWeakLimit













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "Strip" => preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)
local notation "mu" => volume.restrict (interior m64AnnulusDomain)



theorem auxiliaryCircle_observed_continuous_energy_limit
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (e : Q.charts.Point → E) (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    (B : Q.charts.Point → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = (Q.flow.metric time).inner q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : Q.charts.Point) (v : E),
      v ∈ range (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q) → ‖v‖ ^ 2 ≤ C * B q v v)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod) (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (q0 q1 : Q.circle.Point)
    {lo hi : ℝ} (hlo : 0 < lo) (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
    (A : ∀ j, M64Annulus (Q.flow.metric time)
      ((auxiliaryCircleSection Q q0 ∘ gamma0) ∘ (sigma0 j).map)
      ((auxiliaryCircleSection Q q1 ∘ gamma1) ∘ (sigma1 j).map))
    (hA : ∀ j, ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 (A j).map Strip)
    (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi)
    {E0 : ℝ} (henergy : Tendsto
      (fun j => m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) (r j)) atTop (𝓝 E0)) :
    ∃ (r0 : ℝ) (L0 L1 : ℝ → ℝ)
      (L : M64ObservedWeakAnnulus (n := (n + 1) + 1) e
        ((auxiliaryCircleSection Q q0 ∘ gamma0) ∘ L0)
        ((auxiliaryCircleSection Q q1 ∘ gamma1) ∘ L1)),
      r0 ∈ Icc lo hi ∧ Continuous L0 ∧ Continuous L1 ∧ Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L.weightedEnergy B r0 ≤ E0 := by
  classical
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let c0 := auxiliaryCircleSection Q q0 ∘ gamma0
  let c1 := auxiliaryCircleSection Q q1 ∘ gamma1
  have hc0 : Continuous c0 := (auxiliaryCircle_section_contMDiff Q q0).continuous.comp
    hgamma0.continuous
  have hc1 : Continuous c1 := (auxiliaryCircle_section_contMDiff Q q1).continuous.comp
    hgamma1.continuous
  have hperiod0 : Function.Periodic c0 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q q0) (hp0 x)
  have hperiod1 : Function.Periodic c1 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q q1) (hp1 x)
  choose W hmap henergyW using fun j =>
    m64ObservedWeakAnnulus_exists_seed_with_weightedEnergy (A j) e he B hdiag
  have hWE (j : ℕ) (s : ℝ) : (W j).weightedEnergy B s =
      m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) s := henergyW j s
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto
    (fun j => m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) (r j))
      henergy).exists_norm_le
  have hbound (j : ℕ) : m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) (r j) ≤ R :=
    (le_abs_self _).trans (hR _ (mem_range_self j))
  let D := max lo⁻¹ hi
  have hD : 0 ≤ D := (inv_nonneg.mpr hlo.le).trans (le_max_left _ _)
  have hcols (j : ℕ) (i : Fin 2) : ‖(W j).column i‖ ^ 2 ≤ 2 * C * D * R := by
    calc
      _ ≤ 2 * C * (W j).energy B :=
        (W j).column_norm_sq_le_energy B hB hei.isEmbedding hb hpos hC hcoercive i
      _ ≤ 2 * C * (D * (W j).weightedEnergy B (r j)) :=
        mul_le_mul_of_nonneg_left
          ((W j).energy_le_weightedEnergy_of_mem B hB hei.isEmbedding hb hpos hlo (hr j))
          (by positivity)
      _ = (2 * C * D) * m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) (r j) := by
        rw [hWE]
        ring
      _ ≤ (2 * C * D) * R := mul_le_mul_of_nonneg_left (hbound j) (by positivity)
  obtain ⟨r0, hr0, k, hk, hrlim⟩ := isCompact_Icc.tendsto_subseq hr
  obtain ⟨l, L0, L1, hl, hcL0, hcL1, hm0, hm1, hpL0, hpL1, -, -, hlim0, hlim1⟩ :=
    auxiliaryCircle_free_labels_continuous_limit P Q time gamma0 gamma1 hgamma0 hgamma1
      hp0 hp1 hramp0 hramp1 q0 q1 hlo (fun j => sigma0 (k j)) (fun j => sigma1 (k j))
      (fun j => A (k j)) (fun j => hA (k j)) (fun j => r (k j)) (fun j => hr (k j))
      R (fun j => hbound (k j))
  have ht0 (x : ℝ) : Tendsto (fun j => c0 ((sigma0 (k (l j))).map x))
      atTop (𝓝 (c0 (L0 x))) := by
    have h := (hc0.tendsto (L0 x)).comp (hlim0 x)
    have heq (j : ℕ) : c0 ((normalizedDegreeOneLift (sigma0 (k (l j)))).map x) =
        c0 ((sigma0 (k (l j))).map x) :=
      congrFun (normalizedDegreeOneLift_trace hperiod0 (sigma0 (k (l j)))) x
    simpa only [Function.comp_def, heq] using h
  have ht1 (x : ℝ) : Tendsto (fun j => c1 ((sigma1 (k (l j))).map x))
      atTop (𝓝 (c1 (L1 x))) := by
    have h := (hc1.tendsto (L1 x)).comp (hlim1 x)
    have heq (j : ℕ) : c1 ((normalizedDegreeOneLift (sigma1 (k (l j)))).map x) =
        c1 ((sigma1 (k (l j))).map x) :=
      congrFun (normalizedDegreeOneLift_trace hperiod1 (sigma1 (k (l j)))) x
    simpa only [Function.comp_def, heq] using h
  obtain ⟨s, L, hs, -, hw, ha⟩ := observedWeakAnnulus_varying_trace_subsequence e he hei hread
    (fun j => hc0.comp (degreeOneLift_continuous (sigma0 (k (l j)))))
    (fun j => hc1.comp (degreeOneLift_continuous (sigma1 (k (l j)))))
    (Eventually.of_forall ht0) (Eventually.of_forall ht1)
    (fun j => W (k (l j))) (fun j i => hcols (k (l j)) i)
  have hrall : Tendsto (fun j => r (k (l (s j)))) atTop (𝓝 r0) :=
    hrlim.comp (hl.comp hs).tendsto_atTop
  have hlsc := varying_trace_weightedEnergy_le_liminf hei.isEmbedding B hB hK hb hpos hsymm
    hlo hr0 (fun j => r (k (l (s j)))) (fun j => hr (k (l (s j)))) hrall
    (fun j => W (k (l (s j)))) L (fun j i => hcols (k (l (s j))) i) hw ha
  have hElim : Tendsto (fun j => (W (k (l (s j)))).weightedEnergy B (r (k (l (s j)))))
      atTop (𝓝 E0) := by
    simp_rw [hWE]
    exact henergy.comp (hk.comp (hl.comp hs)).tendsto_atTop
  rw [hElim.liminf_eq] at hlsc
  exact ⟨r0, L0, L1, L, hr0, hcL0, hcL1, hm0, hm1, hpL0, hpL1, hlsc⟩

end PoincareConjecture.M64
