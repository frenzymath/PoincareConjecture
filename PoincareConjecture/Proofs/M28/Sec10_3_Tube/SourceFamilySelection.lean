import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CounterexampleSourceNecks

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

structure CounterexampleNeckSegment {epsilon C A D₀ D : ℝ}
    (E : SameTimeCounterexample.{u} epsilon C A D₀ D) where
  path : ℝ → (E.flow.slice E.time).carrier
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper
  upper_lt_one : upper < 1
  path_smooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 path (Icc (0 : ℝ) 1)
  source_region : CounterexampleSourceRegion E path
  length_lt : (E.flow.metric E.time).pathELength path lower upper <
    ENNReal.ofReal ((A + 2 * endpointConnectorBudget epsilon C) *
      E.flow.scalar ⟨E.time, E.basepoint⟩ ^ (-1 / 2 : ℝ))
  lower_scalar : E.flow.scalar ⟨E.time, path lower⟩ =
    16 * (max C 2) ^ 2 * E.flow.scalar ⟨E.time, E.basepoint⟩
  upper_scalar : D * E.flow.scalar ⟨E.time, E.basepoint⟩ <
    2 * (max C 2) ^ 2 * E.flow.scalar ⟨E.time, path upper⟩
  upper_scalar_eq : E.flow.scalar ⟨E.time, path upper⟩ =
    E.flow.scalar ⟨E.time, path 1⟩ / (2 * max C 2)
  scalar_band : ∀ v ∈ Icc lower upper, E.flow.scalar ⟨E.time, path v⟩ ∈
    Icc (16 * (max C 2) ^ 2 * E.flow.scalar ⟨E.time, E.basepoint⟩)
      (E.flow.scalar ⟨E.time, path upper⟩)
  epsilon_lt_half : epsilon < 1 / 2
  cover : NeckOnlyCover (E.flow.metric E.time)
  cover_set : cover.X = path '' Icc lower upper
  cover_epsilon : cover.epsilon = epsilon
  cover_subset_component : cover.X ⊆ source_region.cover.X
  provenance : ∀ N ∈ cover.necks,
    ∃ J : GeneralizedStrongNeck E.flow E.time epsilon,
      N = strongNeck_top J epsilon_lt_half ∧ J.center ∈ cover.X
  neckAt : ∀ v, v ∈ Icc lower upper → GeneralizedStrongNeck E.flow E.time epsilon
  neckAt_center : ∀ v (hv : v ∈ Icc lower upper), (neckAt v hv).center = path v

theorem exists_counterexample_neck_segment_accuracy
    (P : RicciFlowCurvatureTheory.{u}) (T : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (epsilon C A D₀ D : ℝ), 0 < epsilon → epsilon ≤ epsilon₀ →
        0 < C → 0 < D₀ → 32 * (max C 2) ^ 4 ≤ D →
        ∀ E : SameTimeCounterexample.{u} epsilon C A D₀ D,
          Nonempty (CounterexampleNeckSegment E) := by
  classical
  obtain ⟨epsilon₀, hpos, hsmall, hselect⟩ :=
    exists_counterexample_source_necks_accuracy P T
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A D₀ D hepsilon hbound hC hD₀ hD E
  obtain ⟨γ, R, s, t, hs, hst, ht, hγ, hlength, hlo, hhi, hhi_eq, hband,
    hhalf, K, hK, hKepsilon, hKsubset, hprovenance, hcenters⟩ :=
    hselect epsilon C A D₀ D hepsilon hbound hC hD₀ hD E
  exact ⟨{
    path := γ
    lower := s
    upper := t
    lower_pos := hs
    lower_lt_upper := hst
    upper_lt_one := ht
    path_smooth := hγ
    source_region := R
    length_lt := hlength
    lower_scalar := hlo
    upper_scalar := hhi
    upper_scalar_eq := hhi_eq
    scalar_band := hband
    epsilon_lt_half := hhalf
    cover := K
    cover_set := hK
    cover_epsilon := hKepsilon
    cover_subset_component := hKsubset
    provenance := hprovenance
    neckAt := fun v hv => Classical.choose (hcenters v hv)
    neckAt_center := fun v hv => Classical.choose_spec (hcenters v hv) }⟩

structure CounterexampleNeckFamily {epsilon C A : ℝ}
    (E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)) where
  shift : ℕ
  segment : ∀ k : ℕ, CounterexampleNeckSegment (E (k + shift))

theorem exists_counterexample_neck_family_accuracy
    (P : RicciFlowCurvatureTheory.{u}) (T : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (epsilon C A : ℝ), 0 < epsilon → epsilon ≤ epsilon₀ → 0 < C →
        ∀ E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1),
          Nonempty (CounterexampleNeckFamily E) := by
  classical
  obtain ⟨epsilon₀, hpos, hsmall, hselect⟩ :=
    exists_counterexample_neck_segment_accuracy P T
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A hepsilon hbound hC E
  obtain ⟨N, hN⟩ := exists_nat_ge (32 * (max C 2) ^ 4)
  have hsegments : ∀ k : ℕ, Nonempty (CounterexampleNeckSegment (E (k + N))) := by
    intro k
    apply hselect epsilon C A ((k + N : ℕ) + 1) ((k + N : ℕ) + 1)
      hepsilon hbound hC (by positivity)
    exact hN.trans (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
  exact ⟨{ shift := N, segment := fun k => Classical.choice (hsegments k) }⟩

namespace CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

def sourceIndex (H : CounterexampleNeckFamily E) (k : ℕ) : ℕ := k + H.shift

theorem sourceIndex_strictMono (H : CounterexampleNeckFamily E) :
    StrictMono H.sourceIndex := by
  intro i j hij
  exact Nat.add_lt_add_right hij H.shift

end CounterexampleNeckFamily

end PoincareConjecture.M28
