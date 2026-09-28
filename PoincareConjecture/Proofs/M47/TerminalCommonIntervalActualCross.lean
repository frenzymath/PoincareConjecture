import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCrossTail
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalM30Tangent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem terminalCommonInterval_actual_cross_control
    {M : Type v} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (hg : MetricComplete g) (p : M)
    (e : ∀ n, OpenPartialHomeomorph M
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier)
    (he : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (e n) (e n).source)
    (hei : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (e n).symm (e n).target)
    (hbase : ∀ n, e n p = (V.base (G.subsequence n)).2)
    (hE : terminalCommonInterval_compactTangentControl g
      (fun n => M13.scaleSmoothMetric
        ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
        (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n))) e)
    {R lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda) (hlambda_lt : lambda < 1) :
    ∀ᶠ n in atTop,
      let f := terminalCommonInterval_m30TerminalMap G n
      let T := (e n).trans f.symm
      let k := G.limit.flow.metric 0
      let q := G.limit.base
      {z | g.edist p z ≤ ENNReal.ofReal R} ⊆ T.source ∧
        MapsTo T {z | g.edist p z ≤ ENNReal.ofReal R} (k.ball q (4 * (R + 1))) ∧
        {z | k.edist q z ≤ ENNReal.ofReal R} ⊆ T.target ∧
        MapsTo T.symm {z | k.edist q z ≤ ENNReal.ofReal R} (g.ball p (4 * (R + 1))) ∧
        (∀ x, g.edist p x ≤ ENNReal.ofReal R →
          ∀ y, g.edist p y ≤ ENNReal.ofReal R →
            ENNReal.ofReal (lambda ^ 2) * g.edist x y ≤ k.edist (T x) (T y) ∧
            k.edist (T x) (T y) ≤ ENNReal.ofReal (lambda⁻¹ ^ 2) * g.edist x y) ∧
        (∀ x, k.edist q x ≤ ENNReal.ofReal R →
          ∀ y, k.edist q y ≤ ENNReal.ofReal R →
            ENNReal.ofReal (lambda ^ 2) * k.edist x y ≤ g.edist (T.symm x) (T.symm y) ∧
            g.edist (T.symm x) (T.symm y) ≤ ENNReal.ofReal (lambda⁻¹ ^ 2) * k.edist x y) ∧
        T p = q ∧ T.symm q = p ∧
        (∀ z ∈ T.source, f (T z) = e n z ∧ T.symm (T z) = z) ∧
        ∀ z ∈ T.target, e n (T.symm z) = f z ∧ T (T.symm z) = z := by
  let f := terminalCommonInterval_m30TerminalMap G
  let k := G.limit.flow.metric 0
  let h (n : ℕ) : RiemannianMetric 3
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier :=
    M13.scaleSmoothMetric ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
      (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n))
  have hk : MetricComplete k := G.limit.complete 0 G.limit.zero_mem
  have hf : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (f n) (f n).source :=
    fun n => (terminalCommonInterval_m30_terminal_source G n).2.1.of_le (by simp)
  have hfi : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (f n).symm (f n).target :=
    fun n => (terminalCommonInterval_m30_terminal_source G n).2.2.of_le (by simp)
  have hF : terminalCommonInterval_compactTangentControl k h f :=
    fun _ hK _ hl hlt => terminalCommonInterval_m30_terminal_tangent G hK hl hlt
  have hb (n : ℕ) : e n p = f n G.limit.base :=
    (hbase n).trans (terminalCommonInterval_m30_terminal_base G n).symm
  filter_upwards [terminalCommonInterval_eventually_cross_control g k h hg hk e f
    he hei hf hfi p G.limit.base hb hE hF hR hlambda hlambda_lt,
    terminalCommonInterval_eventually_cross_control k g h hk hg f e hf hfi he hei
      G.limit.base p (fun n => (hb n).symm) hF hE hR hlambda hlambda_lt]
    with n hn hn'
  have hp : p ∈ (e n).source := (hn.1 (by
    let : EMetricSpace M := g.toEMetricSpace
    change edist p p ≤ ENNReal.ofReal R
    simp)).1
  have hq : G.limit.base ∈ (f n).source := by
    rw [(terminalCommonInterval_m30_terminal_source G n).1]
    exact G.exhaustion.base_mem n
  have hid := terminalCommonInterval_cross_map_identities (e n) (f n)
    p G.limit.base hp hq (hb n)
  exact ⟨hn.1, hn.2.1, hn'.1, hn'.2.1, hn.2.2, hn'.2.2, hid⟩

end PoincareConjecture.M47
