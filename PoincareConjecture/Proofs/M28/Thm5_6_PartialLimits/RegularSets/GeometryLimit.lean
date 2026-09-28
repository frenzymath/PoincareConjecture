import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.Extraction
import PoincareConjecture.Proofs.M04.TensorNorm
import Mathlib.Analysis.SpecificLimits.Basic












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M28




theorem exists_regular_metric_limit_of_geometry
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    [∀ k, SecondCountableTopology (M k)] [∀ k, PreconnectedSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (D : ∀ k, LeviCivitaData (g k))
    (p : ∀ k, M k) (hn : 1 ≤ n)
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    {δ₀ r₀ κ V : ℝ} (hδ₀ : 0 < δ₀) (hr₀ : 0 < r₀) (hκ : 0 < κ) (hV : 0 ≤ V)
    (hbase : ∀ᶠ k in atTop, p k ∈ regularPoints (g k) δ₀)
    (hvolume : ∀ᶠ k in atTop, (g k).volumeMeasure univ ≤ ENNReal.ofReal V)
    (hnoncollapse : ∀ᶠ k in atTop, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ q ∈ regularComponent (g k) (p k) r,
        (∀ x ∈ (g k).ball q r, |(D k).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
        ENNReal.ofReal (κ * r ^ n) ≤ (g k).volumeMeasure ((g k).ball q r))
    (hcurv : ∀ δ : ℝ, 0 < δ → ∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ regularComponent (g k) (p k) δ,
        (D k).curvatureDerivativeNorm l x ≤ C) :
    Nonempty (RegularPointedMetricConvergence g p) := by
  classical
  let δ : ℕ → ℝ := fun j => (δ₀ / 4) * (1 / 2 : ℝ) ^ j
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hbaselevel (j : ℕ) : 4 * δ j ≤ δ₀ := by
    have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h := mul_le_mul_of_nonneg_left hp hδ₀.le
    dsimp [δ]
    nlinarith only [h]
  have hstep (j : ℕ) : 4 * δ (j + 1) ≤ 2 * δ j := by
    apply le_of_eq
    dsimp [δ]
    rw [pow_succ]
    ring
  have hcofinal (ε : ℝ) (hε : 0 < ε) : ∃ j, 4 * δ j ≤ ε := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
    have ht : Tendsto (fun j => 4 * δ j) atTop (𝓝 (0 : ℝ)) := by
      simpa only [δ, mul_zero] using (hp.const_mul (δ₀ / 4)).const_mul 4
    obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds hε)).exists
    exact ⟨j, hj.le⟩
  have hcurvlevel : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ regularComponent (g k) (p k) (2 * δ j),
        (D k).curvatureDerivativeNorm l x ≤ C := by
    intro j l
    exact hcurv (2 * δ j) (mul_pos (by norm_num) (hδ j)) l
  choose K hK hKtail using fun j => hcurvlevel j 0
  choose R ρ N hρ hρR _hRδ _hρr₀ hfactory using fun j =>
    exists_uniform_regular_normal_cover n hn (hK j) (hδ j) hr₀ hκ hV
  have hcovers : ∀ j, ∀ᶠ k in atTop,
      Nonempty (RegularNormalChartCover (g k) (p k) (δ j) (R j) (ρ j) (N j)) := by
    intro j
    filter_upwards [hbase, hvolume, hnoncollapse, hKtail j] with k hbk hvk hnk hck
    apply hfactory j (M k) (g k) (D k) (p k)
      (regularPoints_antitone (g k) (hbaselevel j) hbk) ?_ hnk hvk
    intro x hx
    simpa only [(D k).curvatureDerivativeNorm_zero] using hck x hx
  exact exists_regular_metric_limit_of_eventual_normal_covers D hρ hρR hstep
    hcofinal hdist hcurvlevel hcovers

end PoincareConjecture.M28
