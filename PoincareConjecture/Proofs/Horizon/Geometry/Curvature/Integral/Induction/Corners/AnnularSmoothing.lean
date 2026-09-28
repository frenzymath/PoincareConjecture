import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactAnnulus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.CornerNeighborhood

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Bundle Topology
namespace PoincareConjecture.RiemannianMetric

theorem exists_annular_distance_smoothing_with_common_level_constraints
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -K ≤ D.sectionalCurvature x v w)
    (p : M) {ι : Type*} [Finite ι] (f h : ι → M → ℝ)
    {U : Set M} (hU : IsOpen U)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hpair : ∀ i x, x ∈ U →
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1 ∧
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δ)
    (hhess : ∀ i x, x ∈ U → ∀ v : TangentSpace (𝓡 n) x,
      D.hessian (f i) x v v ≤ C * g.inner x v v ∧
      D.hessian (h i) x v v ≤ C * g.inner x v v)
    {r R R' : ℝ} (hr : 0 < r) (hRR : R < R')
    (hball : ∀ x, g.edist p x ≤ ENNReal.ofReal R' → x ∈ U)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ rho : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      ∀ x : M, r ≤ (g.edist p x).toReal → (g.edist p x).toReal ≤ R →
        |rho x - (g.edist p x).toReal| ≤ ε ∧
        g.tangentNorm x (D.gradient rho x) ≤ 1 + η ∧
        (∀ v : TangentSpace (𝓡 n) x,
          D.hessian rho x v v ≤ (4 / (3 * r) + K * R' / 4 + η) * g.inner x v v) ∧
        ((∀ i, f i x = f i p) → ∀ i,
          |g.inner x (D.gradient rho x) (D.gradient (f i) x)| ≤
            4 * Real.sqrt δ + C * R' / 2 + η ∧
          |g.inner x (D.gradient rho x) (D.gradient (h i) x)| ≤
            4 * Real.sqrt δ + C * R' / 2 + η) := by
  let T := {y : M | r ≤ (g.edist p y).toReal ∧ (g.edist p y).toReal ≤ R}
  let S := {y : M | (r ≤ (g.edist p y).toReal ∧ (g.edist p y).toReal ≤ R) ∧
    ∀ i, f i y = f i p}
  have hT : IsCompact T := g.isCompact_real_distance_annulus hc p r R
  have hS : IsCompact S :=
    g.isCompact_commonLevel_distance_annulus hc p r R f
      (fun i => (hf i).continuous) (fun i => f i p)
  obtain ⟨rho, hrho, herr, hgrad, hess, hcross⟩ :=
    g.exists_distance_smoothing_on_compact_with_common_level_constraints
      D hc hK hsec p f h hU (fun i => (hf i).contMDiffOn)
      (fun i => (hh i).contMDiffOn) hδ hC hpair hhess hT hS.isClosed
      (fun _ hy => hy.1) hr (fun _ hy => ⟨hy.1, hy.2.trans_lt hRR⟩)
      hball (fun i _ hy => hy.2 i) hε hη
  refine ⟨rho, hrho, ?_⟩
  intro x hx hx'
  exact ⟨herr x ⟨hx, hx'⟩, hgrad x ⟨hx, hx'⟩, hess x ⟨hx, hx'⟩,
    fun hlevel i => hcross i x ⟨⟨hx, hx'⟩, hlevel⟩⟩

end PoincareConjecture.RiemannianMetric
