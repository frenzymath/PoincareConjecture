import PoincareConjecture.Proofs.M11.IntervalOpenInclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {IM : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {IN : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

theorem interval_product_smooth_of_local (K : SpacetimeInterval)
    {B : Type*} (J : B → SpacetimeInterval) (hsub : ∀ b, (J b).domain ⊆ K.domain)
    (ho : ∀ b, IsOpen {t : K.domain | t.val ∈ (J b).domain})
    (hc : ∀ t : K.domain, ∃ b, t.val ∈ (J b).domain)
    (f : (smoothInterval K).Point × M → N)
    (hf : ∀ b, ContMDiff ((𝓡∂ 1).prod IM) IN ∞
      (f ∘ Prod.map (spacetimeIntervalInclusion (smoothInterval (J b))
        (smoothInterval K) (hsub b)) id)) :
    ContMDiff ((𝓡∂ 1).prod IM) IN ∞ f := by
  let := intervalChartedSpace K
  intro p
  obtain ⟨b, hb⟩ := hc p.1
  let := intervalChartedSpace (J b)
  let e := intervalInclusionHomeomorph K (J b) (hsub b) (ho b)
  have hp : p.1 ∈ e.target := by
    dsimp [e, intervalInclusionHomeomorph]
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨⟨p.1.val, hb⟩, Subtype.ext rfl⟩
  have hi := (intervalInclusionHomeomorph_inverse_smooth K (J b) (hsub b) (ho b)).contMDiffAt
    (e.open_target.mem_nhds hp)
  apply ((hf b).contMDiffAt.comp p
    ((hi.comp p contMDiffAt_fst).prodMk contMDiffAt_snd)).congr_of_eventuallyEq
  filter_upwards [(e.open_target.preimage continuous_fst).mem_nhds hp] with q hq
  change f q = f (e (e.symm q.1), q.2)
  rw [e.right_inv hq]

theorem interval_product_differential_surjective (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain) (ho : IsOpen {t : K.domain | t.val ∈ L.domain})
    (p : (smoothInterval L).Point × M) :
    Function.Surjective (mfderiv ((𝓡∂ 1).prod IM) ((𝓡∂ 1).prod IM)
      (Prod.map (spacetimeIntervalInclusion (smoothInterval L) (smoothInterval K) h)
        (id : M → M)) p) := by
  let := intervalChartedSpace K
  let := intervalChartedSpace L
  rw [mfderiv_prodMap ((smoothInterval_inclusion_smooth L K h p.1).mdifferentiableAt (by simp))
    mdifferentiableAt_id, mfderiv_id]
  intro v
  let e := (intervalInclusion_localDiffeomorph K L h ho p.1).mfderivToContinuousLinearEquiv
    (by simp)
  obtain ⟨w, hw⟩ := e.surjective v.1
  exact ⟨(w, v.2), Prod.ext hw rfl⟩

end PoincareConjecture.Proofs.M11
