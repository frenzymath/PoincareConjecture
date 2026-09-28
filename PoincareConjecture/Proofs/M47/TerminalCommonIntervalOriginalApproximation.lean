import PoincareConjecture.Proofs.M47.TerminalCommonIntervalPerturbedCapture
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCrossTail
import PoincareConjecture.Proofs.M36.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v w z

namespace PoincareConjecture.M47

private theorem original_source_edist_comm
    {X : Type w} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (h : RiemannianMetric 3 X) (x y : X) : h.edist x y = h.edist y x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨h.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm



theorem terminalCommonInterval_original_approximation
    {M : Type u} {N : Type v} {X : ℕ → Type w} {Z : Type z}
    [TopologicalSpace M] [TopologicalSpace N] [∀ n, TopologicalSpace (X n)]
    [T3Space M] [T3Space N] [∀ n, T2Space (X n)]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [PreconnectedSpace M] [PreconnectedSpace N]
    [∀ n, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (g : RiemannianMetric 3 M) (k : RiemannianMetric 3 N)
    (h : ∀ n, RiemannianMetric 3 (X n)) (hg : MetricComplete g) (hk : MetricComplete k)
    (e : ∀ n, OpenPartialHomeomorph M (X n))
    (f : ∀ n, OpenPartialHomeomorph N (X n))
    (he : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (e n) (e n).source)
    (hf : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (f n) (f n).source)
    (hfi : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (f n).symm (f n).target)
    (p : M) (q : N) (hbase : ∀ n, e n p = f n q)
    (hE : terminalCommonInterval_compactTangentControl g h e)
    (hF : terminalCommonInterval_compactTangentControl k h f)
    (iota : Z → M) (K : Set Z) (hK : IsCompact (iota '' K))
    (a : ∀ n, Z → X n)
    (happrox : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop, ∀ z ∈ K,
      (h n).edist (a n z) (e n (iota z)) < ENNReal.ofReal eta)
    (I : M → N)
    (hconv : letI := k.toMetricSpace
      TendstoUniformlyOn (fun n z => (f n).symm (e n (iota z))) (I ∘ iota) atTop K) :
    letI := k.toMetricSpace
    ∃ R : ℝ, 0 < R ∧
      (∀ᶠ n in atTop, ∀ z ∈ K,
        a n z ∈ (f n).target ∧ (f n).symm (a n z) ∈ k.ball q R) ∧
      TendstoUniformlyOn (fun n z => (f n).symm (a n z)) (I ∘ iota) atTop K := by
  let := g.toMetricSpace
  let := k.toMetricSpace
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall p
  let R := max 1 R0
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hinside (z : Z) (hz : z ∈ K) : g.edist p (iota z) ≤ ENNReal.ofReal R := by
    change iota z ∈ {x | g.edist p x ≤ ENNReal.ofReal R}
    rw [← g.toMetricSpace_closedBall p hR.le]
    exact Metric.closedBall_subset_closedBall (le_max_right _ _)
      (hR0 (mem_image_of_mem iota hz))
  let D := 2 * (R + 1) + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalf_lt : (1 / 2 : ℝ) < 1 := by norm_num
  have hgeom : ∀ᶠ n in atTop, ∀ z ∈ K,
      a n z ∈ (f n).target ∧ (f n).symm (a n z) ∈ k.ball q (2 * D) ∧
        k.edist ((f n).symm (a n z)) ((f n).symm (e n (iota z))) ≤
          (2 : ℝ≥0∞) * (h n).edist (a n z) (e n (iota z)) := by
    filter_upwards [
      hE _ (g.isCompact_closedBall_of_metricComplete hg p (R + 1)) _ hhalf hhalf_lt,
      hF _ (k.isCompact_closedBall_of_metricComplete hk q (4 * (2 * D + 1)))
        _ hhalf hhalf_lt,
      happrox 1 zero_lt_one] with n hnE hnF hnApprox
    have hforward := g.image_ball_subset_ball_of_tangentNorm_le (h n) (e n) p
      (by norm_num : (0 : ℝ) < 2)
      (fun z hz => hnE.1 (show g.edist p z ≤ ENNReal.ofReal (R + 1) from hz.le))
      (fun z hz => (he n z hz).contMDiffAt ((e n).open_source.mem_nhds hz))
      (fun z hz v => by simpa using (hnE.2 z
        (show g.edist p z ≤ ENNReal.ofReal (R + 1) from hz.le) v).2)
    have hcapture := terminalCommonInterval_inverse_capture_distance k (h n) hk
      (f n) (hf n) (hfi n) q hD hnF.1
      (by simpa only [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num] using hnF.2)
    intro z hz
    have hzball : iota z ∈ g.ball p (R + 1) :=
      (hinside z hz).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
        (by positivity : 0 < R + 1)).mpr (by linarith))
    have heSmall := hforward (mem_image_of_mem (e n) hzball)
    rw [hbase n] at heSmall
    have heD : e n (iota z) ∈ (h n).ball (f n q) D :=
      heSmall.trans_le (ENNReal.ofReal_le_ofReal (by dsimp only [D]; linarith))
    have haD : a n z ∈ (h n).ball (f n q) D := by
      have hsmall := hnApprox z hz
      rw [original_source_edist_comm (h n) (a n z) (e n (iota z))] at hsmall
      change (h n).edist (f n q) (a n z) < ENNReal.ofReal D
      calc
        _ ≤ (h n).edist (f n q) (e n (iota z)) +
            (h n).edist (e n (iota z)) (a n z) := M36.metric_edist_triangle _ _ _ _
        _ < ENNReal.ofReal (2 * (R + 1)) + ENNReal.ofReal 1 :=
          ENNReal.add_lt_add heSmall hsmall
        _ = ENNReal.ofReal D := by
          rw [← ENNReal.ofReal_add (by positivity) (by norm_num)]
    exact ⟨(hcapture.1 _ haD).1, (hcapture.1 _ haD).2, hcapture.2 _ haD _ heD⟩
  refine ⟨2 * D, by positivity, ?_, ?_⟩
  · filter_upwards [hgeom] with n hn z hz
    exact ⟨(hn z hz).1, (hn z hz).2.1⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro eps heps
    have hc := Metric.tendstoUniformlyOn_iff.mp hconv (eps / 2) (by positivity)
    filter_upwards [hgeom, happrox (eps / 4) (by positivity), hc] with n hn ha hc z hz
    have herror : k.edist ((f n).symm (a n z)) ((f n).symm (e n (iota z))) <
        ENNReal.ofReal (eps / 2) := by
      calc
        _ ≤ (2 : ℝ≥0∞) * (h n).edist (a n z) (e n (iota z)) := (hn z hz).2.2
        _ < (2 : ℝ≥0∞) * ENNReal.ofReal (eps / 4) := by
          exact ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) (ha z hz)
        _ = ENNReal.ofReal (eps / 2) := by
          rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
    have hdist : dist ((f n).symm (e n (iota z))) ((f n).symm (a n z)) < eps / 2 := by
      rw [dist_comm]
      exact edist_lt_ofReal.mp herror
    have hcross : dist (I (iota z)) ((f n).symm (e n (iota z))) < eps / 2 := hc z hz
    exact (dist_triangle (I (iota z)) ((f n).symm (e n (iota z)))
      ((f n).symm (a n z))).trans_lt (by linarith)

end PoincareConjecture.M47
