import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.OppositeCross
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient.LevelDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Bundle Topology InnerProductSpace BigOperators

namespace PoincareConjecture.LeviCivitaData

theorem abs_sum_increment_le_of_opposite_gradient_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (p x : M) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpair : ∀ z, g.edist p z ≤ g.edist p x →
      g.tangentNorm z (D.gradient f z) ≤ 1 ∧
      g.tangentNorm z (D.gradient h z) ≤ 1 ∧
      g.inner z (D.gradient f z) (D.gradient h z) ≤ -1 + 2 * δ) :
    |(f x + h x) - (f p + h p)| ≤ 2 * Real.sqrt δ * (g.edist p x).toReal := by
  let := g.toMetricSpace
  apply g.abs_sub_le_mul_toReal_edist_of_gradient_bound_closedBall hc
    (hf.add hh) p x (L := ⟨2 * Real.sqrt δ, by positivity⟩)
  intro z hz
  have hz' : g.edist p z ≤ g.edist p x := by
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top p z),
      ← ENNReal.ofReal_toReal (g.edist_ne_top p x)]
    apply ENNReal.ofReal_le_ofReal
    change dist p z ≤ (g.edist p x).toReal
    simpa only [Metric.mem_closedBall, dist_comm z p] using hz
  obtain ⟨hfn, hhn, hop⟩ := hpair z hz'
  change g.tangentNorm z (D.gradient (fun y => f y + h y) z) ≤ _
  rw [D.gradient_add ((hf z).mdifferentiableAt (by simp))
    ((hh z).mdifferentiableAt (by simp))]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Poincare.CurvatureIntegral.norm_add_le_of_opposite
    (D.gradient f z) (D.gradient h z) hδ hfn hhn hop



theorem abs_partner_increment_le_of_opposite_gradient_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (p x : M) {δ q : ℝ} (hδ : 0 ≤ δ)
    (hpair : ∀ z, g.edist p z ≤ g.edist p x →
      g.tangentNorm z (D.gradient f z) ≤ 1 ∧
      g.tangentNorm z (D.gradient h z) ≤ 1 ∧
      g.inner z (D.gradient f z) (D.gradient h z) ≤ -1 + 2 * δ)
    (hgap : |f x - f p| ≤ q) :
    |h x - h p| ≤ 2 * Real.sqrt δ * (g.edist p x).toReal + q := by
  have hsum := D.abs_sum_increment_le_of_opposite_gradient_bounds hc hf hh p x hδ hpair
  calc
    |h x - h p| = |((f x + h x) - (f p + h p)) - (f x - f p)| := by congr 1; ring
    _ ≤ |(f x + h x) - (f p + h p)| + |f x - f p| := abs_sub _ _
    _ ≤ _ := add_le_add hsum hgap



theorem abs_centered_strainer_tilt_error_le
    {n k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) (f h : Fin k → M → ℝ) (u : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    (p x : M) {δ q a : ℝ} (hδ : 0 ≤ δ) (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hpair : ∀ i z, g.edist p z ≤ g.edist p x →
      g.tangentNorm z (D.gradient (f i) z) ≤ 1 ∧
      g.tangentNorm z (D.gradient (h i) z) ≤ 1 ∧
      g.inner z (D.gradient (f i) z) (D.gradient (h i) z) ≤ -1 + 2 * δ)
    (hgap : ∀ i, |f i x - f i p| ≤ q) :
    let β := a / ((k : ℝ) + 1)
    let F := fun y => (1 - a) * u y + β * ∑ i, h i y
    |F x - (1 - a) * u x - β * ∑ i, h i p| ≤
      a * (2 * Real.sqrt δ * (g.edist p x).toReal + q) := by
  dsimp only
  let β := a / ((k : ℝ) + 1)
  let B := 2 * Real.sqrt δ * (g.edist p x).toReal + q
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hβeq : β * ((k : ℝ) + 1) = a := by
    dsimp only [β]
    exact div_mul_cancel₀ a (by positivity)
  have hβk : β * (k : ℝ) ≤ a := by nlinarith
  have hsum : |∑ i, (h i x - h i p)| ≤ (k : ℝ) * B := by
    calc
      _ ≤ ∑ i : Fin k, |h i x - h i p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, B := Finset.sum_le_sum (fun i _ =>
        D.abs_partner_increment_le_of_opposite_gradient_bounds
          hc (hf i) (hh i) p x hδ (hpair i) (hgap i))
      _ = _ := by simp
  change |(1 - a) * u x + β * ∑ i, h i x - (1 - a) * u x -
    β * ∑ i, h i p| ≤ a * B
  calc
    _ = |β * ∑ i, (h i x - h i p)| := by
      congr 1
      rw [Finset.sum_sub_distrib]
      ring
    _ = β * |∑ i, (h i x - h i p)| := by rw [abs_mul, abs_of_nonneg hβ]
    _ ≤ β * ((k : ℝ) * B) := mul_le_mul_of_nonneg_left hsum hβ
    _ ≤ a * B := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hβk hB

end PoincareConjecture.LeviCivitaData
