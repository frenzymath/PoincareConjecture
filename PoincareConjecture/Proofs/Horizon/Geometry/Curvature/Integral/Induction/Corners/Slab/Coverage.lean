import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.OppositeValue
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.Parameters
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.StripCenters


set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle Topology BigOperators
namespace PoincareConjecture.LeviCivitaData
theorem centered_tilt_mem_shifted_inner_band
    {n k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) (f h : Fin k → M → ℝ) (u : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    (p x : M) {Δ δ r z : ℝ} (hΔ : 0 < Δ)
    (hΔsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1)))
    (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ ((Δ / (8 * ((k : ℝ) + 1))) / 256) ^ 2)
    (hr : 0 < r) (hx : (g.edist p x).toReal ≤ 2 * r)
    (hpair : ∀ i y, g.edist p y ≤ g.edist p x →
      g.tangentNorm y (D.gradient (f i) y) ≤ 1 ∧
      g.tangentNorm y (D.gradient (h i) y) ≤ 1 ∧
      g.inner y (D.gradient (f i) y) (D.gradient (h i) y) ≤ -1 + 2 * δ)
    (hlevel : ∀ i, f i x = f i p) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε ^ 2 / 2048
    let τ := 1 / (1 + σ ^ 2 / 8)
    let s := τ * r / 1024
    let a := Δ / 4
    let β := a / ((k : ℝ) + 1)
    let F := fun y => (1 - a) * u y + β * ∑ i, h i y
    let b := (1 - a) * z + β * ∑ i, h i p
    |u x - z| ≤ s / 128 →
      F x - b + s / 16 ∈ Icc (3 * s / 64) (5 * s / 64) := by
  dsimp only
  let ε := Δ / (8 * ((k : ℝ) + 1))
  let σ := ε ^ 2 / 2048
  let τ := 1 / (1 + σ ^ 2 / 8)
  let s := τ * r / 1024
  let a := Δ / 4
  let β := a / ((k : ℝ) + 1)
  let F := fun y => (1 - a) * u y + β * ∑ i, h i y
  let b := (1 - a) * z + β * ∑ i, h i p
  change |u x - z| ≤ s / 128 → F x - b + s / 16 ∈ Icc (3 * s / 64) (5 * s / 64)
  intro hnear
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * ((k : ℝ) + 1))).mp hΔsmall
    dsimp [a]
    nlinarith [mul_nonneg hk hΔ.le]
  have hs : 0 < s := by dsimp [s, τ]; positivity
  have he := D.abs_centered_strainer_tilt_error_le hc f h u hf hh p x hδ
    (q := 0) le_rfl ha hpair (fun i => by rw [hlevel i]; simp)
  change |F x - (1 - a) * u x - β * ∑ i, h i p| ≤ _ at he
  have hemargin : 4 * a * Real.sqrt δ * r ≤ s / 256 :=
    Poincare.CurvatureIntegral.tilted_slab_inner_margin_of_small_parameter
      hΔ hΔsmall hδ hδsmall hr
  have herror : |F x - (1 - a) * u x - β * ∑ i, h i p| ≤ s / 256 := by
    apply he.trans
    have hhx := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ a * (2 * Real.sqrt δ))
    nlinarith
  have hnear' : |(1 - a) * (u x - z)| ≤ s / 128 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - a)]
    exact (mul_le_mul_of_nonneg_left hnear (by linarith)).trans (by nlinarith)
  have htotal : |F x - b| ≤ s / 256 + s / 128 := by
    calc
      |F x - b| = |(F x - (1 - a) * u x - β * ∑ i, h i p) +
        (1 - a) * (u x - z)| := by congr 1; dsimp [b]; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add herror hnear')
  rcases abs_le.mp htotal with ⟨hl, hu⟩
  constructor <;> linarith
theorem exists_tilted_inner_band_covering_radial_point
    {n k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) (f h : Fin k → M → ℝ) (u : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    (p x : M) {Δ δ r : ℝ} (hΔ : 0 < Δ)
    (hΔsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1)))
    (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ ((Δ / (8 * ((k : ℝ) + 1))) / 256) ^ 2)
    (hr : 0 < r)
    (hx : (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16))
    (hpair : ∀ i y, g.edist p y ≤ g.edist p x →
      g.tangentNorm y (D.gradient (f i) y) ≤ 1 ∧
      g.tangentNorm y (D.gradient (h i) y) ≤ 1 ∧
      g.inner y (D.gradient (f i) y) (D.gradient (h i) y) ≤ -1 + 2 * δ)
    (hlevel : ∀ i, f i x = f i p) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε ^ 2 / 2048
    let τ := 1 / (1 + σ ^ 2 / 8)
    let s := τ * r / 1024
    let a := Δ / 4
    let β := a / ((k : ℝ) + 1)
    let F := fun y => (1 - a) * u y + β * ∑ i, h i y
    |u x - τ * (g.edist p x).toReal| ≤ τ * (r / 65536) →
      ∃ t ∈ Poincare.CurvatureIntegral.normalizedStripCenters,
        (t : ℝ) * r ∈ Icc (7 * r / 12) (9 * r / 10) ∧
        u x ∈ Ioo (2 * τ * ((t : ℝ) * r) - s / 4)
          (2 * τ * ((t : ℝ) * r) + s / 4) ∧
        F x - ((1 - a) * (2 * τ * ((t : ℝ) * r)) + β * ∑ i, h i p) + s / 16 ∈
          Icc (3 * s / 64) (5 * s / 64) := by
  dsimp only
  let ε := Δ / (8 * ((k : ℝ) + 1))
  let σ := ε ^ 2 / 2048
  let τ := 1 / (1 + σ ^ 2 / 8)
  let s := τ * r / 1024
  let a := Δ / 4
  let β := a / ((k : ℝ) + 1)
  let F := fun y => (1 - a) * u y + β * ∑ i, h i y
  change |u x - τ * (g.edist p x).toReal| ≤ τ * (r / 65536) → _
  intro hu
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨t, ht, hnear⟩ :=
    Poincare.CurvatureIntegral.normalizedStripCenters_cover τ r (u x) hτ hr
      (Poincare.CurvatureIntegral.normalized_radial_value_mem_cover_interval hτ hr hx hu)
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · have hlo := mul_le_mul_of_nonneg_right t.property.1 hr.le
    have hhi := mul_le_mul_of_nonneg_right t.property.2 hr.le
    constructor <;> nlinarith
  · change u x ∈ Ioo (2 * τ * ((t : ℝ) * r) - s / 4)
      (2 * τ * ((t : ℝ) * r) + s / 4)
    change |u x - 2 * τ * ((t : ℝ) * r)| ≤ s / 128 at hnear
    rcases abs_le.mp hnear with ⟨hl, hu⟩
    constructor <;> linarith
  · exact D.centered_tilt_mem_shifted_inner_band hc f h u hf hh p x
      hΔ hΔsmall hδ hδsmall hr (by linarith [hx.2]) hpair hlevel hnear
end PoincareConjecture.LeviCivitaData
