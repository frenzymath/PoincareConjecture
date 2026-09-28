import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Maps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem relative_pullback_inner_eq
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (k : ℕ) {t : ℝ} (ht : t ∈ Ioo c d)
    (hmetric : (F (G.subsequence k)).metricAt t = (H (L.subsequence k)).metricAt t)
    {U : Set G.limitCarrier.carrier} (hU : IsOpen U)
    (f : G.limitCarrier.carrier → L.limitCarrier.carrier)
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hfU : MapsTo f U (L.exhaustion k))
    (heq : ∀ x ∈ U,
      ((L.embedding k).toFun (t, f x)).2 = ((G.embedding k).toFun (t, x)).2)
    (x : G.limitCarrier.carrier) (hx : x ∈ U) (v w : G.limitCarrier.tangent x) :
    pullbackInnerValue L.limitFlow (H (L.subsequence k)) (L.embedding k) t (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) =
        pullbackInnerValue G.limitFlow (F (G.subsequence k)) (G.embedding k) t x v w := by
  let p := fun y ↦ ((L.embedding k).toFun (t, y)).2
  let q := fun y ↦ ((G.embedding k).toFun (t, y)).2
  have hlocal : p ∘ f =ᶠ[𝓝 x] q := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq y hy
  have hderiv := mfderiv_comp x
    (((L.embedding k).spatialMap_contMDiffAt (L.exhaustion_open k) ht
      (hfU hx)).mdifferentiableAt (by simp))
    ((hf x hx).mdifferentiableAt (by simp))
  have hchain : (mfderiv (𝓡 n) (𝓡 n) p (f x)).comp
      (mfderiv (𝓡 n) (𝓡 n) f x) = mfderiv (𝓡 n) (𝓡 n) q x :=
    hderiv.symm.trans hlocal.mfderiv_eq
  have hv := congrArg (fun A ↦ A v) hchain
  have hw := congrArg (fun A ↦ A w) hchain
  change ((H (L.subsequence k)).metricAt t).inner (p (f x))
      (mfderiv (𝓡 n) (𝓡 n) p (f x) (mfderiv (𝓡 n) (𝓡 n) f x v))
      (mfderiv (𝓡 n) (𝓡 n) p (f x) (mfderiv (𝓡 n) (𝓡 n) f x w)) =
    ((F (G.subsequence k)).metricAt t).inner (q x)
      (mfderiv (𝓡 n) (𝓡 n) q x v) (mfderiv (𝓡 n) (𝓡 n) q x w)
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  rw [hv, hw, show p (f x) = q x from heq x hx, hmetric]

theorem eventually_relative_tangentNorm_bounds
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
    {r D : ℝ} (hr : 0 < r) (hD : 1 < D) :
    ∀ᶠ k in atTop,
      let f := fun x ↦ ((L.embedding k).inverse
        (0, ((G.embedding k).toFun (0, x)).2)).2
      ∀ x ∈ G.limitFlow.ballAt 0 r, ∀ v : G.limitCarrier.tangent x,
        L.limitCarrier.metricNorm (L.limitFlow.metricAt 0) (f x)
            (mfderiv (𝓡 n) (𝓡 n) f x v) ≤
          D ^ 2 * G.limitCarrier.metricNorm (G.limitFlow.metricAt 0) x v ∧
        G.limitCarrier.metricNorm (G.limitFlow.metricAt 0) x v ≤
          D ^ 2 * L.limitCarrier.metricNorm (L.limitFlow.metricAt 0) (f x)
            (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  have hGK : IsCompact (closure (G.limitFlow.ballAt 0 r)) :=
    (G.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hGcomplete
      G.limitFlow.base r
  have hLK : IsCompact (closure (L.limitFlow.ballAt 0 (4 * r))) :=
    (L.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hLcomplete
      L.limitFlow.base (4 * r)
  have hU : IsOpen (G.limitFlow.ballAt 0 r) := by
    let := G.limitCarrier.metricEMetricSpace (G.limitFlow.metricAt 0)
    change IsOpen {x | edist G.limitFlow.base x < ENNReal.ofReal r}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  obtain ⟨j, hj⟩ := L.exists_exhaustion_superset hLK
  filter_upwards [eventually_relative_map_smooth C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource hr,
    G.eventually_pullback_tangentNorm_bounds hGK hGtime hD,
    L.eventually_pullback_tangentNorm_bounds hLK hLtime hD,
    eventually_ge_atTop j] with k hk hG hL hjk
  let f := fun x ↦ ((L.embedding k).inverse
    (0, ((G.embedding k).toFun (0, x)).2)).2
  have hfE : MapsTo f (G.limitFlow.ballAt 0 r) (L.exhaustion k) :=
    fun x hx ↦ L.exhaustion_monotone hjk (hj (subset_closure (hk.1 hx)))
  dsimp only
  intro x hx v
  have hid := relative_pullback_inner_eq C F H G L k hLtime (hmetric k)
    hU f hk.2.1 hfE hk.2.2 x hx v v
  have hG' := hG x (subset_closure hx) v
  have hL' := hL (f x) (subset_closure (hk.1 hx)) (mfderiv (𝓡 n) (𝓡 n) f x v)
  rw [hid] at hL'
  have hDp : 0 ≤ D := (zero_lt_one.trans hD).le
  constructor
  · calc
      _ ≤ D * Real.sqrt (pullbackInnerValue G.limitFlow (F (G.subsequence k))
          (G.embedding k) 0 x v v) := hL'.2
      _ ≤ D * (D * G.limitCarrier.metricNorm (G.limitFlow.metricAt 0) x v) :=
        mul_le_mul_of_nonneg_left hG'.1 hDp
      _ = _ := by ring
  · calc
      _ ≤ D * Real.sqrt (pullbackInnerValue G.limitFlow (F (G.subsequence k))
          (G.embedding k) 0 x v v) := hG'.2
      _ ≤ D * (D * L.limitCarrier.metricNorm (L.limitFlow.metricAt 0) (f x)
          (mfderiv (𝓡 n) (𝓡 n) f x v)) := mul_le_mul_of_nonneg_left hL'.1 hDp
      _ = _ := by ring

end PoincareConjecture.PointedGeometricConvergence
