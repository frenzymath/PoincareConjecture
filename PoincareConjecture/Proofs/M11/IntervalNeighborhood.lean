import PoincareConjecture.Proofs.M11.IntervalTopology

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.Proofs.M11

theorem interval_exists_small_neighborhood (I : SpacetimeInterval) (t : I.domain)
    {U : Set I.domain} (hU : U ∈ 𝓝 t) :
    ∃ J : SpacetimeInterval, ∃ h : J.domain ⊆ I.domain,
      t.val ∈ J.domain ∧ {s : I.domain | s.val ∈ J.domain} ∈ 𝓝 t ∧
        ∀ s : J.domain, (⟨s.val, h s.property⟩ : I.domain) ∈ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  let S : Set ℝ := I.domain ∩ Metric.ball t.val r
  have htS : t.val ∈ S := ⟨t.property, Metric.mem_ball_self hr⟩
  have hacc : AccPt t.val (𝓟 S) :=
    ((interval_uniqueDiffOn I t.val t.property).inter (Metric.ball_mem_nhds _ hr)).accPt
  obtain ⟨s, hs, hst⟩ := accPt_iff_nhds.mp hacc univ univ_mem
  let J : SpacetimeInterval := {
    domain := S
    ordConnected := ((interval_convex I).inter (convex_ball _ _)).ordConnected
    nontrivial := ⟨s, hs.2, t.val, htS, hst⟩
  }
  refine ⟨J, inter_subset_left, htS, ?_, ?_⟩
  · have he : {s : I.domain | s.val ∈ J.domain} = Metric.ball t r := by
      ext s
      change (s.val ∈ I.domain ∧ dist s.val t.val < r) ↔ dist s t < r
      simp only [s.property, true_and, Subtype.dist_eq]
    rw [he]
    exact Metric.ball_mem_nhds t hr
  · intro s
    apply hrU
    exact s.property.2

end PoincareConjecture.Proofs.M11
