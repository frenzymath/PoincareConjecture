import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalEndpoint
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology









set_option autoImplicit false
open Set Filter Geometry
open scoped Topology

namespace PoincareConjecture.M76

private theorem segment_inter_subset_singleton_of_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p u v : E}
    (h : ∀ᶠ x in 𝓝 p, x ∈ segment ℝ p u ∩ segment ℝ p v → x = p) :
    segment ℝ p u ∩ segment ℝ p v ⊆ {p} := by
  intro x hx
  by_contra hxp
  have hpx : p ≠ x := Ne.symm hxp
  have hc : Tendsto (AffineMap.lineMap p x) (𝓝 (0 : ℝ)) (𝓝 p) := by
    simpa using (AffineMap.lineMap_continuous (R := ℝ) (p := p) (q := x)).tendsto 0
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      AffineMap.lineMap p x t ∈ segment ℝ p u ∩ segment ℝ p v →
        AffineMap.lineMap p x t = p :=
    (hc.eventually h).filter_mono nhdsWithin_le_nhds
  have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, hte, ht1, ht0⟩ := (he.and (ht.and self_mem_nhdsWithin)).exists
  have hseg : AffineMap.lineMap p x t ∈ segment ℝ p x :=
    lineMap_mem_segment ℝ p x ⟨le_of_lt ht0, le_of_lt ht1⟩
  have hmem : AffineMap.lineMap p x t ∈ segment ℝ p u ∩ segment ℝ p v :=
    ⟨(convex_segment p u).segment_subset (left_mem_segment ℝ p u) hx.1 hseg,
      (convex_segment p v).segment_subset (left_mem_segment ℝ p v) hx.2 hseg⟩
  have hz := (AffineMap.lineMap_injective ℝ hpx)
    ((hte hmem).trans (AffineMap.lineMap_apply_zero p x).symm)
  exact (ne_of_gt ht0) hz

theorem exists_two_segment_germ_of_interval_union
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (D R : ι → Set E) (hD : ∀ i, IsFinitePLBallPair ℝ (D i) (R i))
    (hinter : ∀ i j, i ≠ j → D i ∩ D j ⊆ R i ∩ R j)
    (hend : ∀ p ∈ ⋃ i, R i, {i | p ∈ R i}.ncard = 2)
    {p : E} (hp : p ∈ ⋃ i, D i) :
    ∃ u v : E, u ≠ p ∧ v ≠ p ∧
      segment ℝ p u ∩ segment ℝ p v ⊆ {p} ∧
      ∀ᶠ x in 𝓝 p, x ∈ ⋃ i, D i ↔ x ∈ segment ℝ p u ∪ segment ℝ p v := by
  classical
  have hlocal : ∀ᶠ x in 𝓝 p, ∀ i, p ∉ D i → x ∉ D i := by
    apply eventually_all.mpr
    intro i
    by_cases hi : p ∈ D i
    · exact Eventually.of_forall (fun _ hn => (hn hi).elim)
    · have he : ∀ᶠ x in 𝓝 p, x ∉ D i :=
        (hD i).isCompact.isClosed.isOpen_compl.mem_nhds hi
      exact he.mono (fun _ hx _ => hx)
  by_cases hr : p ∈ ⋃ i, R i
  · obtain ⟨i, j, hij, hpair⟩ := ncard_eq_two.mp (hend p hr)
    have hpi : p ∈ R i := hpair.symm.subset (Or.inl rfl)
    have hpj : p ∈ R j := hpair.symm.subset (Or.inr rfl)
    have howners (k : ι) (hk : p ∈ D k) : k = i ∨ k = j := by
      by_cases hki : k = i
      · exact Or.inl hki
      · exact hpair.subset ((hinter k i hki ⟨hk, (hD i).1 hpi⟩).1)
    obtain ⟨u, hu, hlu⟩ := (hD i).exists_segment_germ_of_mem_boundary hpi
    obtain ⟨v, hv, hlv⟩ := (hD j).exists_segment_germ_of_mem_boundary hpj
    obtain ⟨a, b, hab, hrim⟩ := (hD i).exists_boundary_eq_pair
    have hfinite : (R i \ {p}).Finite := (hrim.symm ▸ (finite_singleton b).insert a).sdiff
    have haway : ∀ᶠ x in 𝓝 p, x ∉ R i \ {p} :=
      hfinite.isClosed.isOpen_compl.mem_nhds (by simp)
    refine ⟨u, v, hu, hv, segment_inter_subset_singleton_of_eventually ?_, ?_⟩
    · filter_upwards [hlu, hlv, haway] with x hxu hxv hxa hx
      have hxr := (hinter i j hij ⟨hxu.mpr hx.1, hxv.mpr hx.2⟩).1
      by_contra hxp
      exact hxa ⟨hxr, hxp⟩
    · filter_upwards [hlocal, hlu, hlv] with x hx hxu hxv
      constructor
      · intro hxD
        obtain ⟨k, hk⟩ := mem_iUnion.mp hxD
        have hpk : p ∈ D k := by by_contra hn; exact hx k hn hk
        rcases howners k hpk with rfl | rfl
        · exact Or.inl (hxu.mp hk)
        · exact Or.inr (hxv.mp hk)
      · exact fun h => h.elim
          (fun hi => mem_iUnion.mpr ⟨i, hxu.mpr hi⟩)
          (fun hj => mem_iUnion.mpr ⟨j, hxv.mpr hj⟩)
  · obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
    have hpri : p ∉ R i := fun h => hr (mem_iUnion.mpr ⟨i, h⟩)
    have howner (j : ι) (hpj : p ∈ D j) : j = i := by
      by_contra hji
      exact hpri ((hinter j i hji ⟨hpj, hpi⟩).2)
    obtain ⟨u, v, hu, hv, hi, hl⟩ := (hD i).exists_two_segment_germ ⟨hpi, hpri⟩
    refine ⟨u, v, hu, hv, hi, ?_⟩
    filter_upwards [hlocal, hl] with x hx hxl
    refine Iff.trans ?_ hxl
    constructor
    · intro hxD
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxD
      have hpj : p ∈ D j := by by_contra hn; exact hx j hn hj
      exact howner j hpj ▸ hj
    · exact fun hi => mem_iUnion.mpr ⟨i, hi⟩

theorem interval_union_graph_degree_two
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] [DecidableEq E]
    (D R : ι → Set E) (hD : ∀ i, IsFinitePLBallPair ℝ (D i) (R i))
    (hinter : ∀ i j, i ≠ j → D i ∩ D j ⊆ R i ∩ R j)
    (hend : ∀ p ∈ ⋃ i, R i, {i | p ∈ R i}.ncard = 2)
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hbound : ∀ a ∈ G.faces, a.card ≤ 2) (hspace : G.space = ⋃ i, D i)
    (p : G.vertices) : (G.vertexAbstractComplex.edgeGraph.neighborSet p).ncard = 2 := by
  obtain ⟨u, v, hu, hv, hi, hl⟩ := exists_two_segment_germ_of_interval_union D R hD
    hinter hend (hspace.subset (G.vertices_subset_space p.property))
  exact G.ncard_neighborSet_eq_two_of_local_segments hG hbound p.property hu hv hi
    (by simpa only [hspace] using hl)

end PoincareConjecture.M76
