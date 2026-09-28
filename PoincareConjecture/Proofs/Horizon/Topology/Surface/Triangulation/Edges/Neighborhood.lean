


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.ArcNeighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Coordinates








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

omit [T2Space M] in


theorem SmoothEdge.exists_two_sided_neighborhood (e : SmoothEdge M) (p : M)
    (hinj : InjOn e.map (Icc (0 : ℝ) 1))
    (hsource : e.map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : Set M} (hs : s ∈ 𝓝 (e.map t)) :
    ∃ W U V : Set M,
      IsOpen W ∧ e.map t ∈ W ∧ W ⊆ s ∧
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Disjoint U V ∧ W \ (e.map '' Icc (0 : ℝ) 1) = U ∪ V ∧
      e.map t ∈ closure U ∩ closure V := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) p
  let f := c ∘ e.map
  have ht_source : e.map t ∈ c.source := hsource ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have ht_target : f t ∈ c.target := c.map_source ht_source
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    c.continuousOn.comp e.smooth.continuousOn (fun u hu => hsource ⟨u, hu, rfl⟩)
  have hf_inj : InjOn f (Icc (0 : ℝ) 1) := by
    intro u hu v hv h
    exact hinj hu hv (c.injOn (hsource ⟨u, hu, rfl⟩) (hsource ⟨v, hv, rfl⟩) h)
  have hnbhd : c.target ∩ c.symm ⁻¹' s ∈ 𝓝 (f t) := by
    apply Filter.inter_mem (c.open_target.mem_nhds ht_target)
    apply (c.continuousAt_symm ht_target).preimage_mem_nhds
    simpa only [f, Function.comp_apply, c.left_inv ht_source] using hs
  obtain ⟨hsm, hreg⟩ := e.contDiffAt_chart_and_deriv_ne_zero p ht ht_source
  obtain ⟨W, U, V, hWopen, htW, hWs, hUopen, hVopen, hUpath, hVpath,
    hdisjoint, hpartition, htclosure⟩ :=
    Poincare.Topology.Plane.Curves.exists_two_sided_arc_neighborhood
      hf hf_inj ht hsm hreg hnbhd
  have hWtarget : W ⊆ c.target := fun _ h => (hWs h).1
  have hUV_W : U ∪ V ⊆ W := by rw [← hpartition]; exact sdiff_subset
  have hUtarget : U ⊆ c.target := subset_union_left.trans (hUV_W.trans hWtarget)
  have hVtarget : V ⊆ c.target := subset_union_right.trans (hUV_W.trans hWtarget)
  have hArcTarget : f '' Icc (0 : ℝ) 1 ⊆ c.target := by
    rintro _ ⟨u, hu, rfl⟩
    exact c.map_source (hsource ⟨u, hu, rfl⟩)
  have hArcImage : c.symm '' (f '' Icc (0 : ℝ) 1) = e.map '' Icc (0 : ℝ) 1 := by
    change c.symm '' ((c ∘ e.map) '' Icc (0 : ℝ) 1) = _
    simpa only [image_image] using! c.symm_image_image_of_subset_source hsource
  have hdiff : c.symm '' (W \ (f '' Icc (0 : ℝ) 1)) =
      (c.symm '' W) \ (e.map '' Icc (0 : ℝ) 1) := by
    rw [(c.symm.injOn.mono hWtarget).image_sdiff,
      c.symm.injOn.image_inter hWtarget hArcTarget, hArcImage]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  refine ⟨c.symm '' W, c.symm '' U, c.symm '' V,
    c.isOpen_image_symm_of_subset_target hWopen hWtarget,
    ⟨f t, htW, c.left_inv ht_source⟩, ?_,
    c.isOpen_image_symm_of_subset_target hUopen hUtarget,
    c.isOpen_image_symm_of_subset_target hVopen hVtarget,
    hUpath.image' (c.continuousOn_symm.mono hUtarget),
    hVpath.image' (c.continuousOn_symm.mono hVtarget),
    hdisjoint.image c.symm.injOn hUtarget hVtarget, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hWs hx).2
  · rw [← hdiff, hpartition, image_union]
  · simpa only [f, Function.comp_apply, c.left_inv ht_source] using
      (c.continuousAt_symm ht_target).continuousWithinAt.mem_closure_image htclosure.1
  · simpa only [f, Function.comp_apply, c.left_inv ht_source] using
      (c.continuousAt_symm ht_target).continuousWithinAt.mem_closure_image htclosure.2



theorem exists_two_sided_edge_family_neighborhood {I : Type v} [Finite I]
    (edge : I → SmoothEdge M) (i : I) (p : M)
    (hinj : InjOn (edge i).map (Icc (0 : ℝ) 1))
    (hsource : (edge i).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (havoid : ∀ j, j ≠ i → (edge i).map t ∉ (edge j).map '' Icc (0 : ℝ) 1)
    {s : Set M} (hs : s ∈ 𝓝 ((edge i).map t)) :
    ∃ W U V : Set M,
      IsOpen W ∧ (edge i).map t ∈ W ∧ W ⊆ s ∧
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Disjoint U V ∧ W \ (⋃ j, (edge j).map '' Icc (0 : ℝ) 1) = U ∪ V ∧
      (edge i).map t ∈ closure U ∩ closure V := by
  let K : Set M := ⋃ j : {j : I // j ≠ i}, (edge j).map '' Icc (0 : ℝ) 1
  have hKcompact : IsCompact K := isCompact_iUnion (fun j =>
    isCompact_Icc.image_of_continuousOn (edge j).smooth.continuousOn)
  have hnotK : (edge i).map t ∉ K := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact havoid j j.2 hj
  have hnbhd : s ∩ Kᶜ ∈ 𝓝 ((edge i).map t) :=
    Filter.inter_mem hs (hKcompact.isClosed.isOpen_compl.mem_nhds hnotK)
  obtain ⟨W, U, V, hWopen, htW, hWs, hUopen, hVopen, hUpath, hVpath,
    hdisjoint, hpartition, htclosure⟩ :=
    (edge i).exists_two_sided_neighborhood p hinj hsource ht hnbhd
  have hdiff : W \ (⋃ j, (edge j).map '' Icc (0 : ℝ) 1) =
      W \ ((edge i).map '' Icc (0 : ℝ) 1) := by
    ext x
    constructor
    · rintro ⟨hx, hnot⟩
      exact ⟨hx, fun h => hnot (mem_iUnion.mpr ⟨i, h⟩)⟩
    · rintro ⟨hx, hnot⟩
      refine ⟨hx, ?_⟩
      intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      by_cases hji : j = i
      · exact hnot (hji ▸ hj)
      · exact (hWs hx).2 (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  exact ⟨W, U, V, hWopen, htW, fun _ h => (hWs h).1, hUopen, hVopen,
    hUpath, hVpath, hdisjoint, hdiff.trans hpartition, htclosure⟩



theorem exists_two_sided_edge_family_neighborhood_of_endpoint_intersections
    {I : Type v} [Finite I] (edge : I → SmoothEdge M) (i : I) (p : M)
    (hinj : InjOn (edge i).map (Icc (0 : ℝ) 1))
    (hsource : (edge i).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    (hmeet : ∀ j, j ≠ i →
      (edge i).map '' Icc (0 : ℝ) 1 ∩ (edge j).map '' Icc (0 : ℝ) 1 ⊆
        {(edge i).map 0, (edge i).map 1})
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {s : Set M} (hs : s ∈ 𝓝 ((edge i).map t)) :
    ∃ W U V : Set M,
      IsOpen W ∧ (edge i).map t ∈ W ∧ W ⊆ s ∧
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Disjoint U V ∧ W \ (⋃ j, (edge j).map '' Icc (0 : ℝ) 1) = U ∪ V ∧
      (edge i).map t ∈ closure U ∩ closure V := by
  apply exists_two_sided_edge_family_neighborhood edge i p hinj hsource ht ?_ hs
  intro j hji hj
  have hpoint := hmeet j hji ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, hj⟩
  rcases hpoint with hzero | hone
  · exact ht.1.ne' (hinj ⟨ht.1.le, ht.2.le⟩ (by simp) hzero)
  · exact ht.2.ne (hinj ⟨ht.1.le, ht.2.le⟩ (by simp) hone)

end PoincareConjecture.Topology.Surface
