import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.UniformExtraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology NNReal

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

local instance carrierPreconnected {n : ℕ} (C : FlowCarrier n) :
    PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩

theorem exists_common_relative_uniformSubsequence
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    (hmetric : ∀ k,
      (F (G.subsequence k)).metricAt 0 = (H (L.subsequence k)).metricAt 0)
    (Q : ℕ → Set G.limitCarrier.carrier) (hQ : ∀ i, IsCompact (Q i))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hQr : ∀ i, Q i ⊆ G.limitFlow.ballAt 0 (r i)) :
    letI := (L.limitFlow.metricAt 0).toMetricSpace
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f : ∀ i, Q i → L.limitCarrier.carrier,
      (∀ i, Continuous (f i)) ∧ ∀ i,
        TendstoUniformly (fun k (x : Q i) ↦ ((L.embedding (σ k)).inverse
          (0, ((G.embedding (σ k)).toFun (0, x.val)).2)).2) (f i) atTop := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let := (G.limitFlow.metricAt 0).toMetricSpace
  let (i : ℕ) : CompactSpace (Q i) := isCompact_iff_compactSpace.mp (hQ i)
  let f (i k : ℕ) (x : Q i) := ((L.embedding k).inverse
    (0, ((G.embedding k).toFun (0, x.val)).2)).2
  apply exists_common_uniformSubsequence_of_eventually_lipschitz f (fun _ ↦ 4)
    L.limitFlow.base (fun i ↦ closure (L.limitFlow.ballAt 0 (4 * r i)))
  · intro i
    exact (L.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hLcomplete
      L.limitFlow.base (4 * r i)
  · intro i
    filter_upwards [eventually_relative_edist_le C F H G L hGtime hLtime
        hGcomplete hLcomplete hsource hmetric (hr i) (by norm_num : (1 : ℝ) < 2),
      eventually_relative_ball_confinement C F H G L hGtime hLtime
        hGcomplete hLcomplete hsource (hr i)] with k hdist hmap
    constructor
    · intro x y
      change (L.limitFlow.metricAt 0).edist (f i k x) (f i k y) ≤
        (4 : ENNReal) * (G.limitFlow.metricAt 0).edist x.val y.val
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, ENNReal.ofReal_ofNat] using
        hdist x.val (hQr i x.property) y.val (hQr i y.property)
    · intro x
      obtain ⟨y, hy, _, hfy⟩ := hmap x.val (hQr i x.property)
      apply subset_closure
      simpa only [f, hfy] using hy

end PoincareConjecture.PointedGeometricConvergence
