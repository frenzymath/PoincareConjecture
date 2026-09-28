import PoincareConjecture.Proofs.M11.IntervalSystem

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_interval_iff (I : SpacetimeInterval)
    {f : M → (smoothInterval I).Point} {x : M} :
    ContMDiffAt J (𝓡∂ 1) ∞ f x ↔
      ContMDiffAt J 𝓘(ℝ) ∞ (Subtype.val ∘ f) x := by
  let := intervalChartedSpace I
  constructor
  · intro hf
    exact ((smoothInterval I).inclusion_smooth (f x)).comp x hf
  · intro hf
    let D := intervalSegmentAt I (f x)
    let : Fact (D.left < D.right) := ⟨D.lt⟩
    let S : Set M := {y | (f y).val ∈ D.window}
    have hS : S ∈ 𝓝 x :=
      hf.continuousAt.preimage_mem_nhds
        (D.open_window.mem_nhds (intervalSegmentAt_mem I (f x)))
    have hproj : ContMDiffWithinAt J (𝓡∂ 1) ∞ (D.toSegment ∘ f) S x := by
      apply (contMDiffOn_projIcc _
        (D.window_subset ⟨intervalSegmentAt_mem I (f x), (f x).property⟩)).comp
        x hf.contMDiffWithinAt
      intro y hy
      exact D.window_subset ⟨hy, (f y).property⟩
    apply contMDiffAt_iff_target.mpr
    refine ⟨tendsto_subtype_rng.mpr hf.continuousAt, ?_⟩
    change ContMDiffAt J 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
      (extChartAt (𝓡∂ 1) (D.toSegment (f x)) ∘ (D.toSegment ∘ f)) x
    exact (contMDiffAt_extChartAt (I := 𝓡∂ 1) (x := D.toSegment (f x))).comp x
      (hproj.contMDiffAt hS)

theorem contMDiff_interval_iff (I : SpacetimeInterval)
    {f : M → (smoothInterval I).Point} :
    ContMDiff J (𝓡∂ 1) ∞ f ↔ ContMDiff J 𝓘(ℝ) ∞ (Subtype.val ∘ f) :=
  forall_congr' fun _ ↦ contMDiffAt_interval_iff I

end PoincareConjecture.Proofs.M11
