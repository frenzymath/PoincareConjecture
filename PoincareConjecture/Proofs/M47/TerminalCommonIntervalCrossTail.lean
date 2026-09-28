import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCrossDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v w

namespace PoincareConjecture.M47

def terminalCommonInterval_compactTangentControl
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {X : ℕ → Type w} [∀ n, TopologicalSpace (X n)]
    [∀ n, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (g : RiemannianMetric 3 M) (h : ∀ n, RiemannianMetric 3 (X n))
    (e : ∀ n, OpenPartialHomeomorph M (X n)) : Prop :=
  ∀ K : Set M, IsCompact K → ∀ lambda : ℝ, 0 < lambda → lambda < 1 →
    ∀ᶠ n in atTop, K ⊆ (e n).source ∧ ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      lambda * g.tangentNorm x v ≤
        (h n).tangentNorm (e n x) (mfderiv (𝓡 3) (𝓡 3) (e n) x v) ∧
      (h n).tangentNorm (e n x) (mfderiv (𝓡 3) (𝓡 3) (e n) x v) ≤
        lambda⁻¹ * g.tangentNorm x v

theorem terminalCommonInterval_eventually_cross_control
    {M : Type u} {N : Type v} {X : ℕ → Type w}
    [TopologicalSpace M] [TopologicalSpace N] [∀ n, TopologicalSpace (X n)]
    [T3Space M] [T3Space N] [∀ n, T2Space (X n)]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [∀ n, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (g : RiemannianMetric 3 M) (k : RiemannianMetric 3 N)
    (h : ∀ n, RiemannianMetric 3 (X n)) (hg : MetricComplete g) (hk : MetricComplete k)
    (e : ∀ n, OpenPartialHomeomorph M (X n))
    (f : ∀ n, OpenPartialHomeomorph N (X n))
    (he : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (e n) (e n).source)
    (hei : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (e n).symm (e n).target)
    (hf : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (f n) (f n).source)
    (hfi : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (f n).symm (f n).target)
    (p : M) (q : N) (hbase : ∀ n, e n p = f n q)
    (hE : terminalCommonInterval_compactTangentControl g h e)
    (hF : terminalCommonInterval_compactTangentControl k h f)
    {R lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda) (hlambda_lt : lambda < 1) :
    ∀ᶠ n in atTop,
      let T := (e n).trans (f n).symm
      {z | g.edist p z ≤ ENNReal.ofReal R} ⊆ T.source ∧
        MapsTo T {z | g.edist p z ≤ ENNReal.ofReal R} (k.ball q (4 * (R + 1))) ∧
        ∀ x, g.edist p x ≤ ENNReal.ofReal R →
          ∀ y, g.edist p y ≤ ENNReal.ofReal R →
            ENNReal.ofReal (lambda ^ 2) * g.edist x y ≤ k.edist (T x) (T y) ∧
            k.edist (T x) (T y) ≤ ENNReal.ofReal (lambda⁻¹ ^ 2) * g.edist x y := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalf_lt : (1 / 2 : ℝ) < 1 := by norm_num
  filter_upwards [
    hE _ (g.isCompact_closedBall_of_metricComplete hg p (R + 1)) _ hhalf hhalf_lt,
    hF _ (k.isCompact_closedBall_of_metricComplete hk q (8 * (R + 1))) _ hhalf hhalf_lt,
    hE _ (g.isCompact_closedBall_of_metricComplete hg p (4 * (R + 1)))
      lambda hlambda hlambda_lt,
    hF _ (k.isCompact_closedBall_of_metricComplete hk q (4 * (4 * (R + 1) + 1)))
      lambda hlambda hlambda_lt] with n hEc hFc hEs hFs
  have hc := terminalCommonInterval_cross_capture g k (h n) hk (e n) (f n)
    (he n) (hf n) (hfi n) p q (hbase n) hR hEc.1 hFc.1
    (fun z hz v => by simpa using (hEc.2 z hz v).2)
    (fun z hz v => by have hb := (hFc.2 z hz v).1; linarith)
  refine ⟨hc.1, hc.2, ?_⟩
  exact terminalCommonInterval_cross_distance g k (h n) hg hk (e n) (f n)
    (he n) (hei n) (hf n) (hfi n) p q hR (by positivity) hlambda
    hEs.1 hFs.1 hEs.2 hFs.2 hc.1
    (fun z hz => (show k.edist q ((e n).trans (f n).symm z) <
      ENNReal.ofReal (4 * (R + 1)) from hc.2 hz).le)

end PoincareConjecture.M47
