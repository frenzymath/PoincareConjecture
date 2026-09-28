import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RampLabelPairLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FreeEnergyLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedAnnulusEnergyIdentity










set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)
local notation "mu" => volume.restrict (interior m64AnnulusDomain)




theorem free_ramp_observed_continuous_energy_limit
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (e : P.charts.Point → E) (he : ContMDiff (𝓡 (n + 1)) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n + 1) e)
    (B : P.charts.Point → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    (hdiag : ∀ (q : P.charts.Point) (v : TangentSpace (𝓡 (n + 1)) q),
      B q (mfderiv (𝓡 (n + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 (n + 1)) (𝓡 m) e q v) = (P.flow.metric t).inner q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : P.charts.Point) (v : E),
      v ∈ range (mfderiv (𝓡 (n + 1)) (𝓡 m) e q) → ‖v‖ ^ 2 ≤ C * B q v v)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hperiod0 : Function.Periodic gamma0 curvePeriod)
    (hperiod1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 t) (hramp1 : M63IsRampAt P gamma1 t)
    {lo hi : ℝ} (hlo : 0 < lo) (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
    (A : ∀ j, M64Annulus (P.flow.metric t)
      (gamma0 ∘ (sigma0 j).map) (gamma1 ∘ (sigma1 j).map))
    (hA : ∀ j, ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (A j).map Strip)
    (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi)
    {E0 : ℝ} (henergy : Tendsto
      (fun j => m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j)) atTop (𝓝 E0)) :
    ∃ (k : ℕ → ℕ) (r0 : ℝ) (L0 L1 : ℝ → ℝ)
      (L : M64ObservedWeakAnnulus (n := n + 1) e (gamma0 ∘ L0) (gamma1 ∘ L1)),
      StrictMono k ∧ r0 ∈ Icc lo hi ∧ Continuous L0 ∧ Continuous L1 ∧
      Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L0 0 ∈ Icc (0 : ℝ) curvePeriod ∧ L1 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      Tendsto (fun j => r (k j)) atTop (𝓝 r0) ∧
      (∀ x, Tendsto (fun j => (normalizedDegreeOneLift (sigma0 (k j))).map x)
        atTop (𝓝 (L0 x))) ∧
      (∀ x, Tendsto (fun j => (normalizedDegreeOneLift (sigma1 (k j))).map x)
        atTop (𝓝 (L1 x))) ∧
      (∀ᵐ p ∂mu, Tendsto (fun j => (A (k j)).map p) atTop (𝓝 (L.map p))) ∧
      L.weightedEnergy B r0 ≤ E0 := by
  classical
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  choose W hmap hWenergy using fun j =>
    m64ObservedWeakAnnulus_exists_seed_with_weightedEnergy (A j) e he B hdiag
  have hWE (j : ℕ) (s : ℝ) : (W j).weightedEnergy B s =
      m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) s := hWenergy j s
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto
    (fun j => m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j))
      henergy).exists_norm_le
  have hbound (j : ℕ) : m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤ R :=
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
      _ = (2 * C * D) * m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) := by
        rw [hWE]
        ring
      _ ≤ (2 * C * D) * R := mul_le_mul_of_nonneg_left (hbound j) (by positivity)
  obtain ⟨r0, hr0, k, hk, hrlim⟩ := isCompact_Icc.tendsto_subseq hr
  obtain ⟨l, L0, L1, hl, hc0, hc1, hm0, hm1, hp0, hp1, h00, h10, hlim0, hlim1⟩ :=
    free_ramp_labels_continuous_limit P t gamma0 gamma1 hgamma0 hgamma1 hperiod0 hperiod1
      hramp0 hramp1 hlo (fun j => sigma0 (k j)) (fun j => sigma1 (k j))
      (fun j => A (k j)) (fun j => hA (k j)) (fun j => r (k j)) (fun j => hr (k j))
      (fun j => (A (k j)).weightedGramEnergy_integrable (r (k j))) R (fun j => hbound (k j))
  have ht0 (x : ℝ) : Tendsto (fun j => gamma0 ((sigma0 (k (l j))).map x))
      atTop (𝓝 (gamma0 (L0 x))) := by
    have h := (hgamma0.continuous.tendsto (L0 x)).comp (hlim0 x)
    have heq (j : ℕ) : gamma0 ((normalizedDegreeOneLift (sigma0 (k (l j)))).map x) =
        gamma0 ((sigma0 (k (l j))).map x) :=
      congrFun (normalizedDegreeOneLift_trace hperiod0 (sigma0 (k (l j)))) x
    simpa only [Function.comp_def, heq] using h
  have ht1 (x : ℝ) : Tendsto (fun j => gamma1 ((sigma1 (k (l j))).map x))
      atTop (𝓝 (gamma1 (L1 x))) := by
    have h := (hgamma1.continuous.tendsto (L1 x)).comp (hlim1 x)
    have heq (j : ℕ) : gamma1 ((normalizedDegreeOneLift (sigma1 (k (l j)))).map x) =
        gamma1 ((sigma1 (k (l j))).map x) :=
      congrFun (normalizedDegreeOneLift_trace hperiod1 (sigma1 (k (l j)))) x
    simpa only [Function.comp_def, heq] using h
  obtain ⟨s, L, hs, -, hw, ha⟩ := observedWeakAnnulus_varying_trace_subsequence e he hei hread
    (fun j => hgamma0.continuous.comp (degreeOneLift_continuous (sigma0 (k (l j)))))
    (fun j => hgamma1.continuous.comp (degreeOneLift_continuous (sigma1 (k (l j)))))
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
  refine ⟨k ∘ l ∘ s, r0, L0, L1, L, hk.comp (hl.comp hs), hr0, hc0, hc1, hm0, hm1,
    hp0, hp1, h00, h10, hrall, fun x => (hlim0 x).comp hs.tendsto_atTop,
    fun x => (hlim1 x).comp hs.tendsto_atTop, ?_, hlsc⟩
  simpa only [Function.comp_apply, hmap] using ha

end PoincareConjecture.M64
