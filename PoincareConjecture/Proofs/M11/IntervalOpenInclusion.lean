import PoincareConjecture.Proofs.M11.TimeRestriction
import PoincareConjecture.Proofs.M11.IntervalMaps
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

theorem intervalInclusion_range (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain) :
    range (spacetimeIntervalInclusion (smoothInterval L) (smoothInterval K) h) =
      {t : (smoothInterval K).Point | t.val ∈ L.domain} := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact s.property
  · intro ht
    exact ⟨⟨t.val, ht⟩, Subtype.ext rfl⟩

theorem intervalInclusion_openEmbedding (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain) (ho : IsOpen {t : K.domain | t.val ∈ L.domain}) :
    IsOpenEmbedding (spacetimeIntervalInclusion (smoothInterval L) (smoothInterval K) h) :=
  ⟨intervalInclusion_embedding intervalSystem K L h, (intervalInclusion_range K L h).symm ▸ ho⟩

noncomputable def intervalInclusionHomeomorph (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain) (ho : IsOpen {t : K.domain | t.val ∈ L.domain}) :
    OpenPartialHomeomorph (smoothInterval L).Point (smoothInterval K).Point := by
  letI : Nonempty (smoothInterval L).Point := L.nontrivial.nonempty.to_subtype
  exact (intervalInclusion_openEmbedding K L h ho).toOpenPartialHomeomorph
    (spacetimeIntervalInclusion (smoothInterval L) (smoothInterval K) h)

theorem intervalInclusionHomeomorph_inverse_smooth (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain) (ho : IsOpen {t : K.domain | t.val ∈ L.domain}) :
    ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞ (intervalInclusionHomeomorph K L h ho).symm
      (intervalInclusionHomeomorph K L h ho).target := by
  let := intervalChartedSpace K
  let := intervalChartedSpace L
  let e := intervalInclusionHomeomorph K L h ho
  intro t ht
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_interval_iff L).mpr
  apply ((smoothInterval K).inclusion_smooth t).congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds ht] with s hs
  exact congrArg Subtype.val (e.right_inv hs)

theorem intervalInclusion_localDiffeomorph (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain) (ho : IsOpen {t : K.domain | t.val ∈ L.domain}) :
    IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) ∞
      (spacetimeIntervalInclusion (smoothInterval L) (smoothInterval K) h) := by
  let := intervalChartedSpace K
  let := intervalChartedSpace L
  intro t
  let e := intervalInclusionHomeomorph K L h ho
  exact ⟨{
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := (smoothInterval_inclusion_smooth L K h).contMDiffOn
    contMDiffOn_invFun := intervalInclusionHomeomorph_inverse_smooth K L h ho
  }, mem_univ t, fun _ _ ↦ rfl⟩

end PoincareConjecture.Proofs.M11
