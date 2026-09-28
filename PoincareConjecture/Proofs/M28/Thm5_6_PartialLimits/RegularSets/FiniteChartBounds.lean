import PoincareConjecture.Proofs.M28.Mathlib.FiniteChartCover
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.ChartBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}

theorem exists_finite_stage_chart_cover (G : RegularPointedMetricConvergence g p)
    (j : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    ∃ s : Finset G.limitCarrier.carrier, ∃ C : G.limitCarrier.carrier → Set G.limitCarrier.carrier,
      (∀ q ∈ s, q ∈ closure (G.exhaustion j) ∧ IsCompact (C q) ∧
        q ∈ interior (C q) ∧ C q ⊆ (extChartAt (𝓡 n) q).source ∩ G.exhaustion (j + 1) ∧
        IsCompact ((extChartAt (𝓡 n) q) '' C q) ∧
        (extChartAt (𝓡 n) q) '' C q ⊆ (extChartAt (𝓡 n) q).target) ∧
      closure (G.exhaustion j) ⊆ ⋃ q ∈ s, interior (C q) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let : LocallyCompactSpace G.limitCarrier.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier
  exact (G.exhaustion_compactClosure j).exists_finite_extChart_cover (𝓡 n)
    (G.exhaustion_open (j + 1)) (G.exhaustion_step j)

variable {ι : Type*} [Finite ι]

theorem exists_eventual_finite_chart_bounds (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : ι → G.limitCarrier.carrier) (K : ι → Set (EuclideanSpace ℝ (Fin n))),
      (∀ i, IsCompact (K i)) → (∀ i, K i ⊆ (extChartAt (𝓡 n) (q i)).target) →
      ∀ m : ℕ, ∃ a b B : ℝ, 0 < a ∧ 0 < b ∧ 1 ≤ B ∧
        ∀ᶠ k in atTop, ∀ i x, x ∈ K i →
          (∀ v : EuclideanSpace ℝ (Fin n),
            a * ‖v‖ ^ 2 ≤ (g (G.subsequence k)).pullbackCoefficients
              (G.embedding k ∘ (extChartAt (𝓡 n) (q i)).symm) x v v ∧
            (g (G.subsequence k)).pullbackCoefficients
              (G.embedding k ∘ (extChartAt (𝓡 n) (q i)).symm) x v v ≤ b * ‖v‖ ^ 2) ∧
          ∀ r ≤ m, ‖iteratedFDeriv ℝ r ((g (G.subsequence k)).pullbackCoefficients
            (G.embedding k ∘ (extChartAt (𝓡 n) (q i)).symm)) x‖ ≤ B := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q K hK htarget m
  choose a b ha hb he using fun i =>
    G.exists_eventual_chart_ellipticity (q i) (K i) (hK i) (htarget i)
  choose c hc hj using fun i : ι × Fin (m + 1) =>
    G.exists_eventual_chart_jet_bound (q i.1) i.2 (K i.1) (hK i.1) (htarget i.1)
  let lower : Option ι → ℝ := fun i => i.elim 1 a
  let a₀ := Finset.univ.inf' Finset.univ_nonempty lower
  let b₀ := 1 + ∑ i, b i
  let B := 1 + ∑ i, c i
  have hlower : ∀ i, 0 < lower i := by
    intro i
    cases i with
    | none => exact zero_lt_one
    | some i => exact ha i
  have ha₀ : 0 < a₀ :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hlower i)
  have ha_le (i : ι) : a₀ ≤ a i := Finset.inf'_le lower (Finset.mem_univ (some i))
  have hb_sum : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => (hb i).le)
  have hc_sum : 0 ≤ ∑ i, c i :=
    Finset.sum_nonneg (fun i _ => (by norm_num : (0 : ℝ) ≤ 1).trans (hc i))
  have hb₀ : 0 < b₀ := by dsimp only [b₀]; linarith
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  have hb_le (i : ι) : b i ≤ b₀ := by
    have h := Finset.single_le_sum (fun j _ => (hb j).le) (Finset.mem_univ i)
    dsimp only [b₀]
    linarith
  have hc_le (i : ι × Fin (m + 1)) : c i ≤ B := by
    have h := Finset.single_le_sum
      (fun j _ => (by norm_num : (0 : ℝ) ≤ 1).trans (hc j)) (Finset.mem_univ i)
    dsimp only [B]
    linarith
  refine ⟨a₀, b₀, B, ha₀, hb₀, hB, ?_⟩
  filter_upwards [Filter.eventually_all.mpr he, Filter.eventually_all.mpr hj] with k hk hkj
  intro i x hx
  constructor
  · intro v
    exact ⟨(mul_le_mul_of_nonneg_right (ha_le i) (sq_nonneg ‖v‖)).trans
      (hk i x hx v).1, (hk i x hx v).2.trans
        (mul_le_mul_of_nonneg_right (hb_le i) (sq_nonneg ‖v‖))⟩
  · intro r hr
    let j : ι × Fin (m + 1) := (i, ⟨r, Nat.lt_succ_of_le hr⟩)
    exact (hkj j x hx).trans (hc_le j)

theorem eventually_finite_chart_jet_error (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : ι → G.limitCarrier.carrier) (K : ι → Set (EuclideanSpace ℝ (Fin n))),
      (∀ i, IsCompact (K i)) → (∀ i, K i ⊆ (extChartAt (𝓡 n) (q i)).target) →
      ∀ (m : ℕ) (delta : ℝ), 0 < delta →
        ∀ᶠ k in atTop, ∀ i x, x ∈ K i → ∀ r ≤ m,
          ‖iteratedFDeriv ℝ r ((g (G.subsequence k)).pullbackCoefficients
              (G.embedding k ∘ (extChartAt (𝓡 n) (q i)).symm)) x -
            iteratedFDeriv ℝ r (G.limitMetric.pullbackCoefficients
              (extChartAt (𝓡 n) (q i)).symm) x‖ ≤ delta := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q K hK htarget m delta hdelta
  have he := Filter.eventually_all.mpr (fun i : ι × Fin (m + 1) =>
    Metric.tendstoUniformlyOn_iff.mp
      (G.metric_jets (q i.1) i.2 (K i.1) (hK i.1) (htarget i.1)) delta hdelta)
  filter_upwards [he] with k hk
  intro i x hx r hr
  have h := hk (i, ⟨r, Nat.lt_succ_of_le hr⟩) x hx
  exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using h)

end PoincareConjecture.M28.RegularPointedMetricConvergence
