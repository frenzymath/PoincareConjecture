import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.ProperSpace









set_option autoImplicit false
open Set Metric Topology
open scoped NNReal

namespace Poincare.Topology

theorem isCompact_closedBall_subtype_of_subset
    {X : Type*} [MetricSpace X] [ProperSpace X] {U : Set X}
    (o : U) {r : ℝ} (hsub : closedBall o.val r ⊆ U) :
    IsCompact (closedBall o r) := by
  exact IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall o.val r)
    (by simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using hsub)

theorem exists_uniform_chart_radius_of_compact
    {X Y ι : Type*} [TopologicalSpace X] [MetricSpace Y]
    {Z : ι → Type*} [∀ i, MetricSpace (Z i)]
    {f : X → Y} (hf : IsOpenEmbedding f)
    {V : Set X} (hV : IsOpen V) {K : Set Y} (hK : IsCompact K)
    (hKV : K ⊆ f '' V)
    (e : ∀ i, Z i → X) (o : ∀ i, Z i) {C : ℝ≥0}
    (he : ∀ i, LipschitzWith C (f ∘ e i)) (hcenter : ∀ i, f (e i (o i)) ∈ K) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, e i '' closedBall (o i) r ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_thickening_subset_open (hf.isOpenMap V hV) hKV
  let r := δ / (2 * ((C : ℝ) + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hCr : (C : ℝ) * r < δ := by
    have hpos : 0 < 2 * ((C : ℝ) + 1) := by positivity
    dsimp [r]
    rw [← mul_div_assoc, div_lt_iff₀ hpos]
    nlinarith [C.coe_nonneg]
  refine ⟨r, hr, ?_⟩
  rintro i _ ⟨z, hz, rfl⟩
  have hdist : dist (f (e i z)) (f (e i (o i))) < δ :=
    ((he i).dist_le_mul z (o i)).trans_lt
      ((mul_le_mul_of_nonneg_left hz C.coe_nonneg).trans_lt hCr)
  obtain ⟨x, hx, heq⟩ := hδV (mem_thickening_iff.mpr ⟨_, hcenter i, hdist⟩)
  exact hf.injective heq ▸ hx

end Poincare.Topology
