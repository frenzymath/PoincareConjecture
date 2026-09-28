


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Gluing








set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]



theorem SmoothEdge.exists_open_edge_eq_subsegment (e : SmoothEdge M)
    (hinj : InjOn e.map (Icc (0 : ℝ) 1)) {a b t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (ht : t ∈ Ioo a b) :
    ∃ W : Set M, IsOpen W ∧ e.map t ∈ W ∧
      W ∩ (e.map '' Icc (0 : ℝ) 1) = W ∩ (e.map '' Icc a b) := by
  let tails := (e.map '' Icc 0 a) ∪ (e.map '' Icc b 1)
  have hleft : Icc (0 : ℝ) a ⊆ Icc (0 : ℝ) 1 := fun _ hs => ⟨hs.1, hs.2.trans ha.2⟩
  have hright : Icc b (1 : ℝ) ⊆ Icc (0 : ℝ) 1 := fun _ hs => ⟨hb.1.trans hs.1, hs.2⟩
  have hmiddle : Icc a b ⊆ Icc (0 : ℝ) 1 := fun _ hs => ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩
  have ht01 : t ∈ Icc (0 : ℝ) 1 := hmiddle ⟨ht.1.le, ht.2.le⟩
  have hcompact : IsCompact tails :=
    (isCompact_Icc.image_of_continuousOn (e.smooth.continuousOn.mono hleft)).union
      (isCompact_Icc.image_of_continuousOn (e.smooth.continuousOn.mono hright))
  have hnot : e.map t ∉ tails := by
    rintro (⟨s, hs, heq⟩ | ⟨s, hs, heq⟩)
    · have hst := hinj (hleft hs) ht01 heq
      exact ht.1.not_ge (hst ▸ hs.2)
    · have hst := hinj (hright hs) ht01 heq
      exact ht.2.not_ge (hst ▸ hs.1)
  refine ⟨tailsᶜ, hcompact.isClosed.isOpen_compl, hnot, ?_⟩
  ext q
  constructor
  · rintro ⟨hq, s, hs, rfl⟩
    refine ⟨hq, s, ?_, rfl⟩
    constructor
    · exact le_of_not_gt (fun hsa => hq (Or.inl ⟨s, ⟨hs.1, hsa.le⟩, rfl⟩))
    · exact le_of_not_gt (fun hbs => hq (Or.inr ⟨s, ⟨hbs.le, hs.2⟩, rfl⟩))
  · rintro ⟨hq, s, hs, rfl⟩
    exact ⟨hq, s, hmiddle hs, rfl⟩



theorem SmoothFace.exists_shared_subsegment_neighborhood
    (f g : SmoothFace M) (i j : Fin 3)
    (hinjf : InjOn (f.boundary i).map (Icc (0 : ℝ) 1))
    (hinjg : InjOn (g.boundary j).map (Icc (0 : ℝ) 1))
    {a b c d t s : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Ioo a b) (hs : s ∈ Ioo c d)
    (hpoint : (f.boundary i).map t = (g.boundary j).map s)
    (hshared : (f.boundary i).map '' Icc a b = (g.boundary j).map '' Icc c d)
    (havoidf : ∀ k, k ≠ i → (f.boundary i).map t ∉ (f.boundary k).map '' Icc (0 : ℝ) 1)
    (havoidg : ∀ k, k ≠ j → (g.boundary j).map s ∉ (g.boundary k).map '' Icc (0 : ℝ) 1) :
    ∃ W : Set M, IsOpen W ∧ (f.boundary i).map t ∈ W ∧
      W ∩ frontier f.carrier = W ∩ ((f.boundary i).map '' Icc a b) ∧
      W ∩ frontier g.carrier = W ∩ ((f.boundary i).map '' Icc a b) := by
  obtain ⟨Wf, hWf, htWf, heqf⟩ :=
    (f.boundary i).exists_open_edge_eq_subsegment hinjf ha hb ht
  obtain ⟨Wg, hWg, hsWg, heqg⟩ :=
    (g.boundary j).exists_open_edge_eq_subsegment hinjg hc hd hs
  let Kf : Set M := ⋃ k : {k : Fin 3 // k ≠ i}, (f.boundary k).map '' Icc (0 : ℝ) 1
  let Kg : Set M := ⋃ k : {k : Fin 3 // k ≠ j}, (g.boundary k).map '' Icc (0 : ℝ) 1
  have hKf : IsCompact Kf := isCompact_iUnion (fun k =>
    isCompact_Icc.image_of_continuousOn (f.boundary k).smooth.continuousOn)
  have hKg : IsCompact Kg := isCompact_iUnion (fun k =>
    isCompact_Icc.image_of_continuousOn (g.boundary k).smooth.continuousOn)
  have hnot : (f.boundary i).map t ∉ Kf ∪ Kg := by
    rintro (hq | hq)
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hq
      exact havoidf k k.property hk
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hq
      exact havoidg k k.property (hpoint ▸ hk)
  let W := (Wf ∩ Wg) ∩ (Kf ∪ Kg)ᶜ
  have hW : IsOpen W := (hWf.inter hWg).inter (hKf.union hKg).isClosed.isOpen_compl
  have hmiddlef : Icc a b ⊆ Icc (0 : ℝ) 1 := fun _ hv => ⟨ha.1.trans hv.1, hv.2.trans hb.2⟩
  have hmiddleg : Icc c d ⊆ Icc (0 : ℝ) 1 := fun _ hv => ⟨hc.1.trans hv.1, hv.2.trans hd.2⟩
  refine ⟨W, hW, ⟨⟨htWf, hpoint ▸ hsWg⟩, hnot⟩, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨hqW, hqfront⟩
      rw [f.boundary_carrier] at hqfront
      obtain ⟨k, hk⟩ := mem_iUnion.mp hqfront
      by_cases hki : k = i
      · subst k
        have hq : q ∈ Wf ∩ ((f.boundary i).map '' Icc (0 : ℝ) 1) := ⟨hqW.1.1, hk⟩
        rw [heqf] at hq
        exact ⟨hqW, hq.2⟩
      · exact False.elim (hqW.2 (Or.inl (mem_iUnion.mpr ⟨⟨k, hki⟩, hk⟩)))
    · rintro ⟨hqW, hq⟩
      exact ⟨hqW, f.boundary_image_subset_frontier i (image_mono hmiddlef hq)⟩
  · ext q
    constructor
    · rintro ⟨hqW, hqfront⟩
      rw [g.boundary_carrier] at hqfront
      obtain ⟨k, hk⟩ := mem_iUnion.mp hqfront
      by_cases hkj : k = j
      · subst k
        have hq : q ∈ Wg ∩ ((g.boundary j).map '' Icc (0 : ℝ) 1) := ⟨hqW.1.2, hk⟩
        rw [heqg, ← hshared] at hq
        exact ⟨hqW, hq.2⟩
      · exact False.elim (hqW.2 (Or.inr (mem_iUnion.mpr ⟨⟨k, hkj⟩, hk⟩)))
    · rintro ⟨hqW, hq⟩
      exact ⟨hqW, g.boundary_image_subset_frontier j (image_mono hmiddleg (hshared ▸ hq))⟩



theorem SmoothFace.mem_interior_union_of_shared_subsegment
    (f g : SmoothFace M) (i j : Fin 3)
    (hfregular : closure (interior f.carrier) = f.carrier)
    (hgregular : closure (interior g.carrier) = g.carrier)
    (hinter : f.carrier ∩ g.carrier ⊆ frontier f.carrier)
    (hinjf : InjOn (f.boundary i).map (Icc (0 : ℝ) 1))
    (hinjg : InjOn (g.boundary j).map (Icc (0 : ℝ) 1))
    {a b c d t s : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Ioo a b) (hs : s ∈ Ioo c d)
    (hpoint : (f.boundary i).map t = (g.boundary j).map s)
    (hshared : (f.boundary i).map '' Icc a b = (g.boundary j).map '' Icc c d)
    (havoidf : ∀ k, k ≠ i → (f.boundary i).map t ∉ (f.boundary k).map '' Icc (0 : ℝ) 1)
    (havoidg : ∀ k, k ≠ j → (g.boundary j).map s ∉ (g.boundary k).map '' Icc (0 : ℝ) 1) :
    (f.boundary i).map t ∈ interior (f.carrier ∪ g.carrier) := by
  obtain ⟨N, hNopen, htN, hNf, hNg⟩ :=
    f.exists_shared_subsegment_neighborhood g i j hinjf hinjg ha hb hc hd
      ht hs hpoint hshared havoidf havoidg
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans_lt ht.1, ht.2.trans_le hb.2⟩
  have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨hc.1.trans_lt hs.1, hs.2.trans_le hd.2⟩
  have hmiddle : Icc a b ⊆ Icc (0 : ℝ) 1 := fun _ hv => ⟨ha.1.trans hv.1, hv.2.trans hb.2⟩
  have hchart : (f.boundary i).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) f.chart).source :=
    (f.boundary_image_subset_frontier i).trans
      (f.isClosed_carrier.frontier_subset.trans f.carrier_subset_chart)
  obtain ⟨W, U, V, hWopen, htW, hWsub, _, _, hUpath, hVpath, _, hpartition, _⟩ :=
    (f.boundary i).exists_two_sided_neighborhood f.chart hinjf hchart ht01
      (hNopen.mem_nhds htN)
  have hfrontf : W ∩ frontier f.carrier ⊆ (f.boundary i).map '' Icc (0 : ℝ) 1 := by
    rintro q ⟨hqW, hqf⟩
    have hq : q ∈ N ∩ frontier f.carrier := ⟨hWsub hqW, hqf⟩
    rw [hNf] at hq
    exact image_mono hmiddle hq.2
  have hfrontg : W ∩ frontier g.carrier ⊆ (f.boundary i).map '' Icc (0 : ℝ) 1 := by
    rintro q ⟨hqW, hqg⟩
    have hq : q ∈ N ∩ frontier g.carrier := ⟨hWsub hqW, hqg⟩
    rw [hNg] at hq
    exact image_mono hmiddle hq.2
  have hdense : Dense ((f.boundary i).map '' Icc (0 : ℝ) 1)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (f.interior_boundary_image i)
  have hWdense : W ⊆ closure (U ∪ V) := by
    rw [← hpartition]
    intro q hq
    apply mem_closure_iff.mpr
    intro O hO hqO
    obtain ⟨z, ⟨hzO, hzW⟩, hzK⟩ :=
      hdense.inter_open_nonempty (O ∩ W) (hO.inter hWopen) ⟨q, hqO, hq⟩
    exact ⟨z, hzO, hzW, hzK⟩
  have htf : (f.boundary i).map t ∈ f.carrier := f.isClosed_carrier.frontier_subset
    (f.boundary_image_subset_frontier i ⟨t, ⟨ht01.1.le, ht01.2.le⟩, rfl⟩)
  have htg : (f.boundary i).map t ∈ g.carrier := by
    rw [hpoint]
    exact g.isClosed_carrier.frontier_subset
      (g.boundary_image_subset_frontier j ⟨s, ⟨hs01.1.le, hs01.2.le⟩, rfl⟩)
  have hcover := Poincare.Topology.subset_union_of_two_sided_neighborhood
    f.isClosed_carrier g.isClosed_carrier hfregular hgregular
    (f.disjoint_interiors_of_inter_subset_frontier g hinter) htf htg
    (hWopen.mem_nhds htW) hpartition hUpath.isConnected.isPreconnected
    hVpath.isConnected.isPreconnected hUpath.nonempty hVpath.nonempty hWdense hfrontf hfrontg
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hWopen.mem_nhds htW) hcover)



theorem mem_interior_union_of_coordinate_triangles_shared_subsegment
    (f g : SmoothFace M)
    (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hFsource : convexHull ℝ (range b) ⊆ F.source)
    (hGsource : convexHull ℝ (range c) ⊆ G.source)
    (hfcarrier : f.carrier = F '' convexHull ℝ (range b))
    (hgcarrier : g.carrier = G '' convexHull ℝ (range c))
    (hfboundary : ∀ k : Fin 3, (f.boundary k).map = F ∘
      affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)))
    (hgboundary : ∀ k : Fin 3, (g.boundary k).map = G ∘
      affineChartSegment (c (k.succAbove 0)) (c (k.succAbove 1)))
    (hinter : f.carrier ∩ g.carrier ⊆ frontier f.carrier)
    (i j : Fin 3)
    (hinjf : InjOn (f.boundary i).map (Icc (0 : ℝ) 1))
    (hinjg : InjOn (g.boundary j).map (Icc (0 : ℝ) 1))
    {a d a' d' t s : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1)
    (ha' : a' ∈ Icc (0 : ℝ) 1) (hd' : d' ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Ioo a d) (hs : s ∈ Ioo a' d')
    (hpoint : (f.boundary i).map t = (g.boundary j).map s)
    (hshared : (f.boundary i).map '' Icc a d = (g.boundary j).map '' Icc a' d') :
    (f.boundary i).map t ∈ interior (f.carrier ∪ g.carrier) := by
  refine f.mem_interior_union_of_shared_subsegment g i j ?_ ?_ hinter hinjf hinjg
    ha hd ha' hd' ht hs hpoint hshared ?_ ?_
  · rw [hfcarrier]
    exact coordinate_triangle_closure_interior F b hFsource
  · rw [hgcarrier]
    exact coordinate_triangle_closure_interior G c hGsource
  · intro k hki
    exact coordinate_triangle_boundary_avoids_other_edges f F b hFsource hfboundary hki.symm
      ⟨ha.1.trans_lt ht.1, ht.2.trans_le hd.2⟩
  · intro k hkj
    exact coordinate_triangle_boundary_avoids_other_edges g G c hGsource hgboundary hkj.symm
      ⟨ha'.1.trans_lt hs.1, hs.2.trans_le hd'.2⟩

end PoincareConjecture.Topology.Surface
