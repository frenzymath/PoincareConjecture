import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Instances.Real.Lemmas









set_option autoImplicit false

open Set Filter Topology Function

namespace PoincareConjecture.M38



theorem exists_uniform_product_ball
    {X E : Type*} [TopologicalSpace X] [CompactSpace X] [PseudoMetricSpace E]
    {U : Set (X × E)} (hU : IsOpen U) (p : E)
    (hp : ∀ x : X, (x, p) ∈ U) :
    ∃ δ > 0, univ ×ˢ Metric.ball p δ ⊆ U := by
  have hslice : (univ : Set X) ×ˢ {p} ⊆ U := by
    rintro ⟨x, y⟩ ⟨_, hy⟩
    have hy' : y = p := hy
    subst y
    exact hp x
  obtain ⟨V, W, _, hW, hV, hpW, hprod⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hU hslice
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hW.mem_nhds (hpW (mem_singleton p)))
  exact ⟨δ, hδ, fun z hz => hprod ⟨hV hz.1, hball hz.2⟩⟩



theorem exists_compact_collar_injective_strip
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (F : X × ℝ → Y) (hF : Continuous F)
    (hzero : Injective (fun x : X => F (x, 0)))
    (hlocal : ∀ x : X, ∃ U ∈ 𝓝 (x, (0 : ℝ)), InjOn F U) :
    ∃ δ > 0, InjOn F (univ ×ˢ Ioo (-δ) δ) := by
  let G : Set ((X × X) × (ℝ × ℝ)) :=
    {z | F (z.1.1, z.2.1) = F (z.1.2, z.2.2) →
      (z.1.1, z.2.1) = (z.1.2, z.2.2)}
  have hleft : Continuous (fun z : (X × X) × (ℝ × ℝ) => (z.1.1, z.2.1)) :=
    continuous_fst.fst.prodMk continuous_snd.fst
  have hright : Continuous (fun z : (X × X) × (ℝ × ℝ) => (z.1.2, z.2.2)) :=
    continuous_fst.snd.prodMk continuous_snd.snd
  have hgood (q : X × X) : (q, (0 : ℝ × ℝ)) ∈ interior G := by
    obtain ⟨x, y⟩ := q
    apply mem_interior_iff_mem_nhds.mpr
    by_cases hxy : x = y
    · subst y
      obtain ⟨U, hU, hi⟩ := hlocal x
      have hl : {z : (X × X) × (ℝ × ℝ) | (z.1.1, z.2.1) ∈ U} ∈
          𝓝 ((x, x), (0 : ℝ × ℝ)) :=
        hleft.continuousAt.preimage_mem_nhds hU
      have hr : {z : (X × X) × (ℝ × ℝ) | (z.1.2, z.2.2) ∈ U} ∈
          𝓝 ((x, x), (0 : ℝ × ℝ)) :=
        hright.continuousAt.preimage_mem_nhds hU
      filter_upwards [hl, hr] with z hzl hzr
      exact hi hzl hzr
    · have hne : F (x, 0) ≠ F (y, 0) := fun heq => hxy (hzero heq)
      filter_upwards [((hF.comp hleft).continuousAt.ne_iff_eventually_ne
        (hF.comp hright).continuousAt).mp hne] with z hz
      exact fun heq => (hz heq).elim
  obtain ⟨δ, hδ, hstrip⟩ := exists_uniform_product_ball isOpen_interior
    (0 : ℝ × ℝ) hgood
  refine ⟨δ, hδ, ?_⟩
  intro p hp q hq heq
  have hball : (p.2, q.2) ∈ Metric.ball (0 : ℝ × ℝ) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq,
      Prod.fst_zero, Prod.snd_zero, sub_zero, sub_zero, max_lt_iff]
    exact ⟨abs_lt.mpr hp.2, abs_lt.mpr hq.2⟩
  have hgoodpair : ((p.1, q.1), (p.2, q.2)) ∈ interior G :=
    hstrip ⟨mem_univ (p.1, q.1), hball⟩
  exact (interior_subset hgoodpair) heq

end PoincareConjecture.M38
