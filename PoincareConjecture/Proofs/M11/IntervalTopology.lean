import PoincareConjecture.Definitions.M11AdaptedAtlas
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.Topology









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.Proofs.M11

theorem interval_convex (I : SpacetimeInterval) : Convex ℝ I.domain :=
  I.ordConnected.convex

theorem interval_interior_nonempty (I : SpacetimeInterval) :
    (interior I.domain).Nonempty :=
  (interval_convex I).nontrivial_iff_nonempty_interior.mp I.nontrivial

theorem interval_uniqueDiffOn (I : SpacetimeInterval) : UniqueDiffOn ℝ I.domain :=
  uniqueDiffOn_convex (interval_convex I) (interval_interior_nonempty I)


theorem interval_mem_frontier_iff (I : SpacetimeInterval) {t : ℝ} (ht : t ∈ I.domain) :
    t ∈ frontier I.domain ↔ IsLeast I.domain t ∨ IsGreatest I.domain t := by
  constructor
  · intro hfront
    by_contra h
    have hleft : ∃ a ∈ I.domain, a < t := by
      by_contra hn
      push Not at hn
      exact h (Or.inl ⟨ht, fun a ha ↦ hn a ha⟩)
    have hright : ∃ b ∈ I.domain, t < b := by
      by_contra hn
      push Not at hn
      exact h (Or.inr ⟨ht, fun b hb ↦ hn b hb⟩)
    obtain ⟨a, ha, hat⟩ := hleft
    obtain ⟨b, hb, htb⟩ := hright
    have hInt : t ∈ interior (Icc a b) := by
      rw [interior_Icc]
      exact ⟨hat, htb⟩
    exact hfront.2 (interior_mono (I.ordConnected.out ha hb) hInt)
  · rintro (hmin | hmax)
    · refine ⟨subset_closure ht, ?_⟩
      intro hInt
      have : t ∈ interior (Ici t) := interior_mono (fun _ hy ↦ hmin.2 hy) hInt
      simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at this
    · refine ⟨subset_closure ht, ?_⟩
      intro hInt
      have : t ∈ interior (Iic t) := interior_mono (fun _ hy ↦ hmax.2 hy) hInt
      simp only [interior_Iic, mem_Iio, lt_self_iff_false] at this


theorem interval_exists_local_segment (I : SpacetimeInterval) {t : ℝ}
    (ht : t ∈ I.domain) :
    ∃ a b : ℝ, a < b ∧ t ∈ Icc a b ∧ Icc a b ⊆ I.domain ∧
      Icc a b ∈ 𝓝[I.domain] t := by
  by_cases hleft : ∃ a ∈ I.domain, a < t
  · obtain ⟨a, ha, hat⟩ := hleft
    by_cases hright : ∃ b ∈ I.domain, t < b
    · obtain ⟨b, hb, htb⟩ := hright
      exact ⟨a, b, hat.trans htb, ⟨hat.le, htb.le⟩, I.ordConnected.out ha hb,
        mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hat htb)⟩
    · refine ⟨a, t, hat, ⟨hat.le, le_rfl⟩, I.ordConnected.out ha ht, ?_⟩
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hat)] with s hs has
      exact ⟨has.le, le_of_not_gt (fun hts ↦ hright ⟨s, hs, hts⟩)⟩
  · have hright : ∃ b ∈ I.domain, t < b := by
      obtain ⟨a, ha, b, hb, hab⟩ := I.nontrivial
      by_contra hn
      have heq : ∀ s ∈ I.domain, s = t := by
        intro s hs
        exact le_antisymm (le_of_not_gt (fun hts ↦ hn ⟨s, hs, hts⟩))
          (le_of_not_gt (fun hst ↦ hleft ⟨s, hs, hst⟩))
      exact hab ((heq a ha).trans (heq b hb).symm)
    obtain ⟨b, hb, htb⟩ := hright
    refine ⟨t, b, htb, ⟨le_rfl, htb.le⟩, I.ordConnected.out ht hb, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htb)] with s hs hsb
    exact ⟨le_of_not_gt (fun hst ↦ hleft ⟨s, hs, hst⟩), hsb.le⟩


theorem interval_exists_segment_germ (I : SpacetimeInterval) {t : ℝ}
    (ht : t ∈ I.domain) :
    ∃ a b : ℝ, a < b ∧ t ∈ Icc a b ∧ Icc a b ⊆ I.domain ∧
      I.domain =ᶠ[𝓝 t] Icc a b := by
  obtain ⟨a, b, hab, ht', hsub, hmem⟩ := interval_exists_local_segment I ht
  refine ⟨a, b, hab, ht', hsub, nhdsWithin_eq_iff_eventuallyEq.mp ?_⟩
  apply le_antisymm
  · exact le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr hmem)
  · exact nhdsWithin_mono t hsub


theorem interval_frontier_of_relatively_open (I J : SpacetimeInterval)
    (hopen : ∃ U : Set ℝ, IsOpen U ∧ J.domain = I.domain ∩ U)
    {t : ℝ} (ht : t ∈ J.domain) :
    t ∈ frontier J.domain ↔ t ∈ frontier I.domain := by
  obtain ⟨U, hU, hJ⟩ := hopen
  have htI : t ∈ I.domain := by rw [hJ] at ht; exact ht.1
  have htU : t ∈ U := by rw [hJ] at ht; exact ht.2
  have hInt : t ∈ interior J.domain ↔ t ∈ interior I.domain := by
    rw [hJ, interior_inter, hU.interior_eq]
    exact and_iff_left htU
  change (t ∈ closure J.domain ∧ t ∉ interior J.domain) ↔
    (t ∈ closure I.domain ∧ t ∉ interior I.domain)
  simp only [subset_closure ht, subset_closure htI, true_and, hInt]

end PoincareConjecture.Proofs.M11
