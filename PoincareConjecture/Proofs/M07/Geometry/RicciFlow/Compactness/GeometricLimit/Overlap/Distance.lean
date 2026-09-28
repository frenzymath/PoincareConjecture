import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Algebra.Order.Field
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

private theorem exists_common_locallyUniform_limits
    {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, LocallyCompactSpace (X i)] [∀ i, SigmaCompactSpace (X i)]
    (f : ∀ i, ℕ → X i → ℝ) (heq : ∀ i, Equicontinuous (f i))
    (hb : ∀ i x, ∃ B : ℝ, ∀ k, |f i k x| ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : ∀ i, C(X i, ℝ),
      ∀ i, TendstoLocallyUniformly (fun k => f i (σ k)) (F i) atTop := by
  let u : ∀ i, ℕ → C(X i, ℝ) := fun i k => ⟨f i k, (heq i).continuous k⟩
  have hc (i : ι) : IsCompact (closure (range (u i))) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun v : C(X i, ℝ) => (v : X i → ℝ))
      (𝔖 := {K | IsCompact K}) (fun _ h => h)
      (show Topology.IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact :
        C(X i, ℝ) → UniformOnFun (X i) ℝ {K | IsCompact K}) from
        ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, by
          rw [ContinuousMap.range_toUniformOnFunIsCompact]
          exact UniformOnFun.isClosed_setOfPred_continuous
            CompactlyCoherentSpace.isCoherentWith⟩)
    · intro K hK
      have h : Equicontinuous (fun v : range (u i) => (v.val : X i → ℝ)) := by
        intro x V hV
        filter_upwards [heq i x V hV] with y hy v
        obtain ⟨k, hk⟩ := v.property
        simpa only [← hk, u, ContinuousMap.coe_mk] using hy k
      exact h.equicontinuousOn K
    · intro K hK x hx
      obtain ⟨B, hB⟩ := hb i x
      refine ⟨Metric.closedBall (0 : ℝ) B, isCompact_closedBall _ _, ?_⟩
      rintro v ⟨k, rfl⟩
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, u,
        ContinuousMap.coe_mk] using hB k
  have : ∀ i, FirstCountableTopology C(X i, ℝ) := fun i => by
    have : Filter.IsCountablyGenerated (uniformity C(X i, ℝ)) := inferInstance
    exact UniformSpace.firstCountableTopology _
  obtain ⟨F, _, σ, hσ, hF⟩ := (isCompact_pi_infinite hc).tendsto_subseq
    (x := fun k i => u i k) (fun k i => subset_closure (mem_range_self k))
  exact ⟨σ, hσ, F, fun i =>
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (tendsto_pi_nhds.mp hF i)⟩

theorem exists_pairwise_limits
    {X : ℕ → Type*} [∀ i, PseudoMetricSpace (X i)]
    [∀ i, LocallyCompactSpace (X i)] [∀ i, SigmaCompactSpace (X i)]
    {M : ℕ → Type*} [∀ k, PseudoMetricSpace (M k)]
    (e : ∀ k i, X i → M k) (L : ℕ → ℝ≥0)
    (he : ∀ k i, LipschitzWith (L i) (e k i))
    (hb : ∀ i j (x : X i) (y : X j), ∃ B : ℝ,
      ∀ k, dist (e k i x) (e k j y) ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ D : ∀ i j, C(X i × X j, ℝ),
      ∀ i j, TendstoLocallyUniformly
        (fun k (p : X i × X j) => dist (e (σ k) i p.1) (e (σ k) j p.2))
        (D i j) atTop := by
  let f (a : ℕ × ℕ) (k : ℕ) (p : X a.1 × X a.2) : ℝ :=
    dist (e k a.1 p.1) (e k a.2 p.2)
  have hlip (a : ℕ × ℕ) (k : ℕ) : LipschitzWith (L a.1 + L a.2) (f a k) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      calc
        dist (f a k x) (f a k y) ≤
            dist (e k a.1 x.1) (e k a.1 y.1) +
              dist (e k a.2 x.2) (e k a.2 y.2) := dist_dist_dist_le _ _ _ _
        _ ≤ (L a.1 : ℝ) * dist x y + (L a.2 : ℝ) * dist x y :=
          add_le_add ((he k a.1).dist_le_mul_of_le (le_max_left _ _))
            ((he k a.2).dist_le_mul_of_le (le_max_right _ _))
        _ = (L a.1 + L a.2 : ℝ≥0) * dist x y := by rw [NNReal.coe_add, add_mul]
  have heq (a : ℕ × ℕ) : Equicontinuous (f a) := by
    apply Metric.equicontinuous_of_continuity_modulus
      (fun r => (L a.1 + L a.2 : ℝ≥0) * r)
    · simpa using (tendsto_const_nhds.mul tendsto_id :
        Tendsto (fun r : ℝ => (L a.1 + L a.2 : ℝ≥0) * r)
          (𝓝 0) (𝓝 ((L a.1 + L a.2 : ℝ≥0) * (0 : ℝ))))
    · intro x y k
      exact (hlip a k).dist_le_mul x y
  obtain ⟨σ, hσ, F, hF⟩ := exists_common_locallyUniform_limits f heq (by
    intro a p
    obtain ⟨B, hB⟩ := hb a.1 a.2 p.1 p.2
    exact ⟨B, fun k => by simpa only [f, abs_of_nonneg dist_nonneg] using hB k⟩)
  exact ⟨σ, hσ, fun i j => F (i, j), fun i j => hF (i, j)⟩

section Relation

variable {ι : Type*} {X : ι → Type*} {M : ℕ → Type*}
  [∀ k, PseudoMetricSpace (M k)]
  {e : ∀ k i, X i → M k} {D : ∀ i j, X i × X j → ℝ}
  (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
    (𝓝 (D i j (x, y))))

include hD

theorem nonneg (i j : ι) (x : X i) (y : X j) : 0 ≤ D i j (x, y) :=
  ge_of_tendsto (hD i j x y) (Eventually.of_forall fun _ => dist_nonneg)

theorem self (i : ι) (x : X i) : D i i (x, x) = 0 := by
  apply tendsto_nhds_unique (hD i i x x)
  simp only [dist_self]
  exact tendsto_const_nhds

theorem comm (i j : ι) (x : X i) (y : X j) : D i j (x, y) = D j i (y, x) := by
  exact tendsto_nhds_unique (hD i j x y) (by simpa only [dist_comm] using hD j i y x)

theorem triangle (i j l : ι) (x : X i) (y : X j) (z : X l) :
    D i l (x, z) ≤ D i j (x, y) + D j l (y, z) :=
  le_of_tendsto_of_tendsto (hD i l x z) ((hD i j x y).add (hD j l y z))
    (Eventually.of_forall fun _ => dist_triangle _ _ _)

theorem zero_trans {i j l : ι} {x : X i} {y : X j} {z : X l}
    (hxy : D i j (x, y) = 0) (hyz : D j l (y, z) = 0) :
    D i l (x, z) = 0 := by
  apply le_antisymm _ (nonneg hD i l x z)
  simpa only [hxy, hyz, add_zero] using triangle hD i j l x y z

def zeroSetoid : Setoid (Σ i, X i) where
  r p q := D p.1 q.1 (p.2, q.2) = 0
  iseqv := ⟨fun p => self hD p.1 p.2,
    fun {p q} hpq => (comm hD q.1 p.1 q.2 p.2).trans hpq,
    fun hpq hqr => zero_trans hD hpq hqr⟩

theorem lower [∀ i, PseudoMetricSpace (X i)]
    (c : ι → ℝ) (he : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (i : ι) (x y : X i) : c i * dist x y ≤ D i i (x, y) :=
  ge_of_tendsto (hD i i x y) (Eventually.of_forall fun k => he k i x y)

theorem upper [∀ i, PseudoMetricSpace (X i)]
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (i : ι) (x y : X i) : D i i (x, y) ≤ (L i : ℝ) * dist x y :=
  le_of_tendsto (hD i i x y) (Eventually.of_forall fun k => (he k i).dist_le_mul x y)

theorem zero_unique [∀ i, MetricSpace (X i)]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (he : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    {i j : ι} {x : X i} {y z : X j}
    (hy : D i j (x, y) = 0) (hz : D i j (x, z) = 0) : y = z := by
  have hyz : D j j (y, z) = 0 :=
    zero_trans hD ((comm hD j i y x).trans hy) hz
  have h := lower hD c he j y z
  rw [hyz] at h
  have hdist : dist y z ≤ 0 := by
    by_contra hpos
    have : 0 < c j * dist y z := mul_pos (hc j) (lt_of_not_ge hpos)
    exact (not_lt_of_ge h) this
  exact dist_le_zero.mp hdist

end Relation

theorem isClosed_zero {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (D : C(X × Y, ℝ)) : IsClosed {p | D p = 0} :=
  isClosed_eq D.continuous continuous_const

end PoincareConjecture.ChartDistance
