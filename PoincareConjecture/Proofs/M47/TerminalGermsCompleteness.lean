import PoincareConjecture.Proofs.M47.TerminalGermsBoundary
import PoincareConjecture.Proofs.M47.TerminalGermsBallTransfer
import PoincareConjecture.Proofs.M35.RawFlow.MetricSpace










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47


theorem terminalGerms_source_ball_coverage
    {M : Type u} [TopologicalSpace M]
    {N : ℕ → Type v} [∀ k, TopologicalSpace (N k)] [∀ k, T2Space (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N k)]
    [∀ k, IsManifold (𝓡 3) ∞ (N k)]
    (h : ∀ k, RiemannianMetric 3 (N k))
    (E : ℕ → Set M) (hE : ∀ j, IsOpen (E j))
    (hcompact : ∀ j, IsCompact (closure (E j)))
    (hstep : ∀ j, closure (E j) ⊆ E (j + 1)) (hmono : Monotone E)
    (p : M) (hp : ∀ j, p ∈ E j) (f : ∀ k, M → N k)
    (hf : ∀ k, Topology.IsOpenEmbedding (fun x : E k => f k x))
    (hescape : ∀ A : ℝ, 0 < A → ∃ j, ∀ᶠ k in atTop,
      ∀ x ∈ frontier (E j), ENNReal.ofReal A ≤ (h k).edist (f k p) (f k x)) :
    ∀ A : ℝ, 0 < A → ∃ j, ∀ᶠ k in atTop,
      (h k).ball (f k p) A ⊆ f k '' E j := by
  intro A hA
  obtain ⟨j, hj⟩ := hescape A hA
  refine ⟨j, ?_⟩
  filter_upwards [hj, eventually_ge_atTop (j + 1)] with k hk hjk
  exact terminalGerms_ball_subset_image (h k) (hf k) (hE j) (hcompact j)
    ((hstep j).trans (hmono hjk)) (hp j) hA hk



theorem terminalGerms_compact_ball_closure
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ → Type v} [∀ k, TopologicalSpace (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N k)]
    [∀ k, IsManifold (𝓡 3) ∞ (N k)]
    (g : RiemannianMetric 3 M) (h : ∀ k, RiemannianMetric 3 (N k))
    (E : ℕ → Set M) (hE : ∀ j, IsOpen (E j)) (hmono : Monotone E)
    (hcompact : ∀ j, IsCompact (closure (E j))) (hcover : (⋃ j, E j) = univ)
    (p : M) (f : ∀ k, M → N k)
    (hf : ∀ k, Topology.IsOpenEmbedding (fun x : E k => f k x))
    (hsmooth : ∀ k, IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (E k))
    (hquad : ∀ K : Set M, IsCompact K → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        (h k).inner (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (f k) x v) ≤ 4 * g.inner x v v)
    (hsource : ∀ A : ℝ, 0 < A → ∃ j, ∀ᶠ k in atTop,
      (h k).ball (f k p) A ⊆ f k '' E j)
    {A : ℝ} (hA : 0 < A) : IsCompact (closure (g.ball p A)) := by
  obtain ⟨j, hj⟩ := hsource (2 * A) (by positivity)
  have hsub : g.ball p A ⊆ E j := by
    intro x hx
    obtain ⟨jx, hjx⟩ : ∃ jx, x ∈ E jx := by
      apply mem_iUnion.mp
      rw [hcover]
      trivial
    have hball := terminalGerms_eventually_mem_ball g h E hE hmono hcover f hsmooth hquad hx
    obtain ⟨k, hkcover, hkball, hkj, hkjx⟩ :=
      (hj.and (hball.and ((eventually_ge_atTop j).and (eventually_ge_atTop jx)))).exists
    obtain ⟨y, hy, heq⟩ := hkcover hkball
    have hyx : y = x := congrArg Subtype.val ((hf k).injective
      (a₁ := ⟨y, hmono hkj hy⟩) (a₂ := ⟨x, hmono hkjx hjx⟩) heq)
    simpa only [hyx] using hy
  exact (hcompact j).of_isClosed_subset isClosed_closure (closure_mono hsub)



theorem terminalGerms_metricComplete_of_compact_balls
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [ConnectedSpace M]
    (g : RiemannianMetric 3 M) (p : M)
    (hcompact : ∀ R : ℝ, 0 < R → IsCompact (closure (g.ball p R))) :
    MetricComplete g := by
  rw [RiemannianMetric.metricComplete_iff_toEMetricSpace]
  let : EMetricSpace M := g.toEMetricSpace
  apply EMetric.complete_of_cauchySeq_tendsto
  intro a ha
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff'.mp ha 1 zero_lt_one
  let d := edist (a N) p
  have hd : d ≠ ⊤ := Poincare.edist_ne_top_of_preconnected _ _
  let R : ℝ := d.toReal + 2
  have hR : 0 < R := by dsimp [R]; positivity
  have htail : ∀ᶠ k in atTop, a k ∈ closure (g.ball p R) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    apply subset_closure
    change edist p (a k) < ENNReal.ofReal R
    rw [edist_comm]
    calc
      edist (a k) p ≤ edist (a k) (a N) + d := edist_triangle _ _ _
      _ < 1 + d := ENNReal.add_lt_add_right hd (hN k hk)
      _ ≤ ENNReal.ofReal R := by
        dsimp [R]
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
          ENNReal.ofReal_toReal hd]
        norm_num
        simpa only [add_comm d] using
          add_le_add_left (by norm_num : (1 : ℝ≥0∞) ≤ 2) d
  obtain ⟨x, _, hx⟩ := (hcompact R hR).isComplete (map a atTop) ha
    (le_principal_iff.mpr htail)
  exact ⟨x, hx⟩



theorem terminalGerms_metricComplete_of_boundary_escape
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [ConnectedSpace M]
    {N : ℕ → Type v} [∀ k, TopologicalSpace (N k)] [∀ k, T2Space (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N k)]
    [∀ k, IsManifold (𝓡 3) ∞ (N k)]
    (g : RiemannianMetric 3 M) (h : ∀ k, RiemannianMetric 3 (N k))
    (E : ℕ → Set M) (hE : ∀ j, IsOpen (E j))
    (hcompact : ∀ j, IsCompact (closure (E j)))
    (hstep : ∀ j, closure (E j) ⊆ E (j + 1)) (hmono : Monotone E)
    (hcover : (⋃ j, E j) = univ) (p : M) (hp : ∀ j, p ∈ E j)
    (f : ∀ k, M → N k)
    (hf : ∀ k, Topology.IsOpenEmbedding (fun x : E k => f k x))
    (hsmooth : ∀ k, IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (E k))
    (hquad : ∀ K : Set M, IsCompact K → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        (h k).inner (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (f k) x v) ≤ 4 * g.inner x v v)
    (hescape : ∀ A : ℝ, 0 < A → ∃ j, ∀ᶠ k in atTop,
      ∀ x ∈ frontier (E j), ENNReal.ofReal A ≤ (h k).edist (f k p) (f k x)) :
    MetricComplete g := by
  apply terminalGerms_metricComplete_of_compact_balls g p
  intro R hR
  exact terminalGerms_compact_ball_closure g h E hE hmono hcompact hcover p f hf
    hsmooth hquad
    (terminalGerms_source_ball_coverage h E hE hcompact hstep hmono p hp f hf hescape) hR

end PoincareConjecture.M47
