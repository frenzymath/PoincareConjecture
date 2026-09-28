import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SourceBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.PathComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem eventually_image_ball_subset_source_ball
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hab : a < 0 ∧ 0 < b)
    {t r C : ℝ} (ht : t ∈ Ioo a b)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (hC : 1 < C) :
    ∀ᶠ k in atTop,
      (fun x ↦ ((G.embedding k).toFun (t, x)).2) '' G.limitFlow.ballAt t r ⊆
        (S.flow (G.subsequence k)).ballAt t (C * r) := by
  let g := G.limitFlow.metricAt t
  let p := G.limitFlow.base
  have hcompact : IsCompact (closure (g.ball p r)) :=
    g.isCompact_closure_ball_of_metricComplete hcomplete p r
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_pullback_tangentNorm_bounds hcompact ht hC,
    eventually_ge_atTop j] with k hk hjk
  let h := (S.flow (G.subsequence k)).metricAt t
  let e := (G.embedding k).spatialHomeomorph (G.exhaustion_open k) ht
  have hsource : g.ball p r ⊆ e.source :=
    subset_closure.trans (hj.trans (G.exhaustion_monotone hjk))
  have he : ∀ x ∈ e.source, ContMDiffAt (𝓡 n) (𝓡 n) 1 e x :=
    fun x hx ↦ ((G.embedding k).spatialMap_contMDiffAt
      (G.exhaustion_open k) ht hx).of_le (by simp)
  have hbound : ∀ x ∈ g.ball p r, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * g.tangentNorm x v :=
    fun x hx v ↦ (hk x (subset_closure hx) v).1
  have hbase : e p = (S.flow (G.subsequence k)).base :=
    congrArg Prod.snd (G.base_preserving_at_time hab k ht)
  change e '' g.ball p r ⊆ h.ball (S.flow (G.subsequence k)).base (C * r)
  simpa only [hbase] using g.image_ball_subset_ball_of_tangentNorm_le h e p
    (zero_lt_one.trans hC) hsource he hbound

theorem eventually_relative_ball_confinement
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ k in atTop, ∀ x ∈ G.limitFlow.ballAt 0 r,
      ∃ y ∈ L.limitFlow.ballAt 0 (4 * r),
        ((L.embedding k).toFun (0, y)).2 = ((G.embedding k).toFun (0, x)).2 ∧
        ((L.embedding k).inverse (0, ((G.embedding k).toFun (0, x)).2)).2 = y := by
  have hLcompact : IsCompact (closure (L.limitFlow.ballAt 0 (4 * r))) :=
    (L.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hLcomplete
      L.limitFlow.base (4 * r)
  obtain ⟨j, hj⟩ := L.exists_exhaustion_superset hLcompact
  filter_upwards [G.eventually_image_ball_subset_source_ball hGtime hGtime hGcomplete
      (by norm_num : (1 : ℝ) < 2),
    L.eventually_source_ball_subset_image_ball hLtime hLtime hLcomplete
      (mul_pos (by norm_num : (0 : ℝ) < 2) hr) (by norm_num : (1 : ℝ) < 2),
    eventually_ge_atTop j] with k hG hL hjk x hx
  have hxsource := hG (mem_image_of_mem _ hx)
  rw [hsource k (2 * r)] at hxsource
  obtain ⟨y, hy, hxy⟩ := hL hxsource
  have hy' : y ∈ L.limitFlow.ballAt 0 (4 * r) := by
    simpa only [show (2 : ℝ) * (2 * r) = 4 * r by ring] using hy
  refine ⟨y, hy', hxy, ?_⟩
  have hyE : y ∈ L.exhaustion k :=
    L.exhaustion_monotone hjk (hj (subset_closure hy'))
  have heq : (L.embedding k).toFun (0, y) =
      (0, ((G.embedding k).toFun (0, x)).2) :=
    Prod.ext ((L.embedding k).time_preserving 0 y) hxy
  simpa only [heq] using congrArg Prod.snd
    ((L.embedding k).left_inverse (0, y) ⟨hLtime, hyE⟩)

theorem eventually_relative_map_smooth
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ k in atTop,
      let f := fun x ↦ ((L.embedding k).inverse
        (0, ((G.embedding k).toFun (0, x)).2)).2
      MapsTo f (G.limitFlow.ballAt 0 r) (L.limitFlow.ballAt 0 (4 * r)) ∧
      (∀ x ∈ G.limitFlow.ballAt 0 r, ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) ∧
      (∀ x ∈ G.limitFlow.ballAt 0 r,
        ((L.embedding k).toFun (0, f x)).2 = ((G.embedding k).toFun (0, x)).2) := by
  obtain ⟨i, hi⟩ := G.exists_exhaustion_superset
    ((G.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hGcomplete
      G.limitFlow.base r)
  obtain ⟨j, hj⟩ := L.exists_exhaustion_superset
    ((L.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hLcomplete
      L.limitFlow.base (4 * r))
  filter_upwards [eventually_relative_ball_confinement C F H G L hGtime hLtime
    hGcomplete hLcomplete hsource hr, eventually_ge_atTop i, eventually_ge_atTop j]
    with k hk hik hjk
  let f := fun x ↦ ((L.embedding k).inverse
    (0, ((G.embedding k).toFun (0, x)).2)).2
  have hf (x) (hx : x ∈ G.limitFlow.ballAt 0 r) : f x ∈ L.limitFlow.ballAt 0 (4 * r) := by
    obtain ⟨y, hy, _, hfy⟩ := hk x hx
    simpa only [f, hfy] using hy
  have heq (x) (hx : x ∈ G.limitFlow.ballAt 0 r) :
      ((L.embedding k).toFun (0, f x)).2 = ((G.embedding k).toFun (0, x)).2 := by
    obtain ⟨y, hy, hxy, hfy⟩ := hk x hx
    simpa only [f, hfy] using hxy
  refine ⟨hf, ?_, heq⟩
  intro x hx
  have hxE : x ∈ G.exhaustion k := G.exhaustion_monotone hik (hi (subset_closure hx))
  have hyE : f x ∈ L.exhaustion k := L.exhaustion_monotone hjk
    (hj (subset_closure (hf x hx)))
  have houter := (L.embedding k).spatialInverse_contMDiffAt (L.exhaustion_open k) hLtime hyE
  rw [heq x hx] at houter
  exact houter.comp x (f := fun z ↦ ((G.embedding k).toFun (0, z)).2)
    ((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hGtime hxE)

end PoincareConjecture.PointedGeometricConvergence
