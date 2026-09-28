import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace PoincareConjecture.PointedGeometricConvergence

theorem exists_common_uniformSubsequence
    {X : ℕ → Type*} [∀ i, PseudoMetricSpace (X i)] [∀ i, CompactSpace (X i)]
    {Y : Type*} [MetricSpace Y]
    (f : ∀ i, ℕ → X i → Y) (D : ℕ → ℝ≥0)
    (hlip : ∀ i k, LipschitzWith (D i) (f i k))
    (T : ℕ → Set Y) (hT : ∀ i, IsCompact (T i))
    (hmap : ∀ i k x, f i k x ∈ T i) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : ∀ i, X i → Y,
      (∀ i, Continuous (F i)) ∧
      ∀ i, TendstoUniformly (fun k ↦ f i (σ k)) (F i) atTop := by
  let b (i k : ℕ) : BoundedContinuousFunction (X i) Y :=
    BoundedContinuousFunction.mkOfCompact ⟨f i k, (hlip i k).continuous⟩
  have hcompact (i : ℕ) : IsCompact (closure (range (b i))) := by
    apply BoundedContinuousFunction.arzela_ascoli (T i) (hT i)
    · rintro g x ⟨k, rfl⟩
      exact hmap i k x
    · apply (LipschitzWith.uniformEquicontinuous
        (fun g : range (b i) ↦ (g.val : X i → Y)) (D i) ?_).equicontinuous
      rintro ⟨g, k, rfl⟩
      exact hlip i k
  let A (i : ℕ) := closure (range (b i))
  let (i : ℕ) : CompactSpace (A i) := isCompact_iff_compactSpace.mp (hcompact i)
  let q (k : ℕ) : ∀ i, A i := fun i ↦ ⟨b i k, subset_closure (mem_range_self k)⟩
  obtain ⟨F, _, σ, hσ, hconv⟩ := isCompact_univ.tendsto_subseq
    (x := q) (fun _ ↦ mem_univ _)
  refine ⟨σ, hσ, fun i ↦ (F i).val, fun i ↦ (F i).val.continuous, ?_⟩
  intro i
  apply (BoundedContinuousFunction.tendsto_iff_tendstoUniformly
    (F := fun k ↦ b i (σ k)) (f := (F i).val)).mp
  exact (continuous_subtype_val.tendsto (F i)).comp
    ((continuous_apply i).tendsto F |>.comp hconv)

theorem exists_common_uniformSubsequence_of_eventually_lipschitz
    {X : ℕ → Type*} [∀ i, PseudoMetricSpace (X i)] [∀ i, CompactSpace (X i)]
    {Y : Type*} [MetricSpace Y]
    (f : ∀ i, ℕ → X i → Y) (D : ℕ → ℝ≥0) (p : Y)
    (T : ℕ → Set Y) (hT : ∀ i, IsCompact (T i))
    (hgood : ∀ i, ∀ᶠ k in atTop,
      LipschitzWith (D i) (f i k) ∧ ∀ x, f i k x ∈ T i) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : ∀ i, X i → Y,
      (∀ i, Continuous (F i)) ∧
      ∀ i, TendstoUniformly (fun k ↦ f i (σ k)) (F i) atTop := by
  classical
  choose N hN using fun i ↦ eventually_atTop.mp (hgood i)
  let g (i k : ℕ) : X i → Y := if N i ≤ k then f i k else fun _ ↦ p
  have hg (i k : ℕ) : LipschitzWith (D i) (g i k) := by
    dsimp only [g]
    split_ifs with hk
    · exact (hN i k hk).1
    · exact (LipschitzWith.const p).weaken (by positivity)
  have hm (i k : ℕ) (x : X i) : g i k x ∈ T i ∪ {p} := by
    dsimp only [g]
    split_ifs with hk
    · exact Or.inl ((hN i k hk).2 x)
    · exact Or.inr rfl
  obtain ⟨σ, hσ, F, hF, hconv⟩ := exists_common_uniformSubsequence g D hg
    (fun i ↦ T i ∪ {p}) (fun i ↦ (hT i).union isCompact_singleton) hm
  refine ⟨σ, hσ, F, hF, fun i ↦ ?_⟩
  apply tendstoUniformlyOn_univ.mp
  apply (tendstoUniformlyOn_univ.mpr (hconv i)).congr
  filter_upwards [hσ.tendsto_atTop.eventually (eventually_ge_atTop (N i))] with k hk
  intro x _
  simp only [g, if_pos hk]

end PoincareConjecture.PointedGeometricConvergence
