import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FreeTraceSubsequence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.VaryingEnergyLiminf















set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "mu" => volume.restrict (interior m64AnnulusDomain)




theorem observedWeakAnnulus_free_energy_limit
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) (c0 c1 : ℝ → M)
    (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {lo hi : ℝ} (hlo : 0 < lo) (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi)
    (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
    (A : ∀ j, M64ObservedWeakAnnulus (n := n) e
      (c0 ∘ (sigma0 j).map) (c1 ∘ (sigma1 j).map))
    {E0 : ℝ} (henergy : Tendsto (fun j => (A j).weightedEnergy B (r j)) atTop (𝓝 E0)) :
    ∃ (k : ℕ → ℕ) (r0 : ℝ) (L0 L1 : ℝ → ℝ)
      (L : M64ObservedWeakAnnulus (n := n) e (c0 ∘ L0) (c1 ∘ L1)),
      StrictMono k ∧ r0 ∈ Icc lo hi ∧
      Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L0 0 ∈ Icc (0 : ℝ) curvePeriod ∧ L1 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      Tendsto (fun j => r (k j)) atTop (𝓝 r0) ∧
      Tendsto (fun j => (A (k j)).value) atTop (𝓝 L.value) ∧
      (∀ i, WeakConverges (fun j => (A (k j)).column i) (L.column i)) ∧
      (∀ᵐ p ∂mu, Tendsto (fun j => (A (k j)).map p) atTop (𝓝 (L.map p))) ∧
      L.weightedEnergy B r0 ≤ E0 := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_range_of_tendsto
      (fun j => (A j).weightedEnergy B (r j)) henergy).exists_norm_le
  have hbound (j : ℕ) : (A j).weightedEnergy B (r j) ≤ R :=
    (le_abs_self _).trans (hR _ (mem_range_self j))
  let D := max lo⁻¹ hi
  have hD : 0 ≤ D := (inv_nonneg.mpr hlo.le).trans (le_max_left _ _)
  have hcols (j : ℕ) (i : Fin 2) : ‖(A j).column i‖ ^ 2 ≤ 2 * C * D * R := by
    calc
      _ ≤ 2 * C * (A j).energy B :=
        (A j).column_norm_sq_le_energy B hB hei.isEmbedding hb hpos hC hcoercive i
      _ ≤ 2 * C * (D * (A j).weightedEnergy B (r j)) :=
        mul_le_mul_of_nonneg_left
          ((A j).energy_le_weightedEnergy_of_mem B hB hei.isEmbedding hb hpos hlo (hr j))
          (by positivity)
      _ = (2 * C * D) * (A j).weightedEnergy B (r j) := by ring
      _ ≤ (2 * C * D) * R := mul_le_mul_of_nonneg_left (hbound j) (by positivity)
  obtain ⟨r0, hr0, k, hk, hrlim⟩ := isCompact_Icc.tendsto_subseq hr
  obtain ⟨l, L0, L1, L, hl, hL0, hL1, hP0, hP1, h00, h10, hv, hw, ha, -, -⟩ :=
    observedWeakAnnulus_free_trace_subsequence e he hei hread c0 c1 hc0 hc1 hp0 hp1
      (fun j => sigma0 (k j)) (fun j => sigma1 (k j))
      (fun j => A (k j)) (fun j i => hcols (k j) i)
  have hrllim : Tendsto (fun j => r (k (l j))) atTop (𝓝 r0) :=
    hrlim.comp hl.tendsto_atTop
  have hlsc := varying_trace_weightedEnergy_le_liminf hei.isEmbedding B hB hK hb
    hpos hsymm hlo hr0 (fun j => r (k (l j))) (fun j => hr (k (l j))) hrllim
    (fun j => A (k (l j))) L (fun j i => hcols (k (l j)) i) hw ha
  have hElim : Tendsto (fun j => (A (k (l j))).weightedEnergy B (r (k (l j))))
      atTop (𝓝 E0) := henergy.comp (hk.comp hl).tendsto_atTop
  rw [hElim.liminf_eq] at hlsc
  exact ⟨k ∘ l, r0, L0, L1, L, hk.comp hl, hr0, hL0, hL1, hP0, hP1,
    h00, h10, hrllim, hv, hw, ha, hlsc⟩

end PoincareConjecture.M64
