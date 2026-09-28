import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.AscendingSlope
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.RegularSlab

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_small_excess_of_local_distance_ascent
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p x : M)
    {T c : ℝ} (hT : 0 < T) (hc0 : 0 ≤ c)
    (hascent : ∀ y : M, (g.edist x y).toReal < T → ∀ s : ℝ, 0 < s →
      ∃ z : M, (g.edist y z).toReal < s ∧
        c * (g.edist y z).toReal < (g.edist p z).toReal - (g.edist p y).toReal) :
    ∃ q : M, (g.edist x q).toReal = T ∧
      (g.edist p x).toReal + (g.edist x q).toReal - (g.edist p q).toReal ≤
        (1 - c) * T := by
  let := g.toMetricSpace
  have hball : IsCompact (Metric.closedBall x T) := by
    rw [g.toMetricSpace_closedBall x hT.le]
    exact g.isCompact_closedBall_of_metricComplete hc x T
  apply Poincare.exists_small_excess_of_local_distance_ascent p hball hT hc0
  intro y hy s hs
  have hxy : (g.edist x y).toReal < T := by
    change dist x y < T
    rw [dist_comm]
    exact hy
  exact hascent y hxy s hs

theorem exists_small_excess_of_annular_distance_ascent
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    {r R T c : ℝ} (hT : 0 < T) (hc0 : 0 ≤ c)
    (hascent : ∀ y : M, r - T < (g.edist p y).toReal →
      (g.edist p y).toReal < R + T → ∀ s : ℝ, 0 < s →
        ∃ z : M, (g.edist y z).toReal < s ∧
          c * (g.edist y z).toReal < (g.edist p z).toReal - (g.edist p y).toReal)
    (x : M) (hrx : r ≤ (g.edist p x).toReal) (hRx : (g.edist p x).toReal ≤ R) :
    ∃ q : M, (g.edist x q).toReal = T ∧
      (g.edist p x).toReal + (g.edist x q).toReal - (g.edist p q).toReal ≤
        (1 - c) * T := by
  apply g.exists_small_excess_of_local_distance_ascent hc p x hT hc0
  intro y hy
  have hdist := abs_le.mp (g.abs_toReal_edist_sub_le p x y)
  exact hascent y (by linarith [hdist.2]) (by linarith [hdist.1])

omit [PreconnectedSpace M] in

theorem exists_proper_regular_slab_of_local_distance_ascent
    [ConnectedSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ v w : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y v w)
    (p : M) {r₀ r₁ R₀ R₁ T ε η c a b : ℝ}
    (hT : 0 < T) (hTr : T < r₀) (hr : r₀ < r₁)
    (hrR : r₁ < R₀) (hR : R₀ < R₁)
    (hε : 0 < ε) (hη : 0 < η) (hc0 : 0 ≤ c)
    (ha : 0 < a) (hab : a < b) (hinner : r₁ + ε < a) (houter : b < R₀ - ε)
    (hsmall : 2 * ε / T +
      (4 / (3 * (r₀ - T)) + K * (R₁ + T) / 4 + η) * T / 2 < c)
    (hascent : ∀ y : M, r₁ - T < (g.edist p y).toReal →
      (g.edist p y).toReal < R₀ + T → ∀ s : ℝ, 0 < s →
        ∃ z : M, (g.edist y z).toReal < s ∧
          c * (g.edist y z).toReal < (g.edist p z).toReal - (g.edist p y).toReal) :
    let H := 4 / (3 * (r₀ - T)) + K * (R₁ + T) / 4 + η
    let L := c - 2 * ε / T - H * T / 2
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      IsProperMap ((Ioo a b).restrictPreimage f) ∧
      (∀ x : M, f x ∈ Ioo a b → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
      (∀ x : M, f x ∈ Ioo a b →
        r₁ < (g.edist p x).toReal ∧ (g.edist p x).toReal < R₀) ∧
      ∀ x : M, r₁ < (g.edist p x).toReal → (g.edist p x).toReal < R₀ →
        |f x - (g.edist p x).toReal| ≤ ε ∧
        L ≤ g.tangentNorm x (D.gradient f x) ∧
        g.tangentNorm x (D.gradient f x) ≤ 1 + η ∧
        ∀ v : TangentSpace (𝓡 n) x, D.hessian f x v v ≤ H * g.inner x v v := by
  have heq : ((1 - c) * T + 2 * ε) / T = 1 - c + 2 * ε / T := by
    field_simp
  have hloss : ((1 - c) * T + 2 * ε) / T +
      (4 / (3 * (r₀ - T)) + K * (R₁ + T) / 4 + η) * T / 2 < 1 := by
    rw [heq]
    linarith only [hsmall]
  have hgeo (x : M) (hx : r₁ < (g.edist p x).toReal)
      (hy : (g.edist p x).toReal < R₀) :
      ∃ q : M, T ≤ (g.edist x q).toReal ∧
        (g.edist p x).toReal + (g.edist x q).toReal - (g.edist p q).toReal ≤
          (1 - c) * T := by
    obtain ⟨q, hq, he⟩ := g.exists_small_excess_of_annular_distance_ascent hc p hT hc0
      hascent x hx.le hy.le
    exact ⟨q, hq.ge, he⟩
  have h := g.exists_proper_regular_slab_of_small_excess D hc hK hsec p hT hTr hr hrR hR
    hε hη ha hab hinner houter hloss hgeo
  dsimp only at h ⊢
  have hL : 1 - ((1 - c) * T + 2 * ε) / T -
      (4 / (3 * (r₀ - T)) + K * (R₁ + T) / 4 + η) * T / 2 =
      c - 2 * ε / T -
        (4 / (3 * (r₀ - T)) + K * (R₁ + T) / 4 + η) * T / 2 := by
    rw [heq]
    ring
  simpa only [hL] using h

end PoincareConjecture.RiemannianMetric
