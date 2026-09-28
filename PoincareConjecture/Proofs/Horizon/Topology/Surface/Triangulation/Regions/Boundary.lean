import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Incidence
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Frontier
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Closure
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

theorem isPreconnected_chart_ball_sdiff_finite (p : M) {r : ℝ} (hr : 0 < r)
    (htarget : ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).target)
    {V : Set M} (hV : V.Finite) :
    IsPreconnected (((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) r) \ V) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) p
  let B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
    OpenPartialHomeomorph.univBall (c p) r
  have hBsource : B.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have hBtarget : B.target = ball (c p) r := OpenPartialHomeomorph.univBall_target _ hr
  have hBmem (z : EuclideanSpace ℝ (Fin 2)) : B z ∈ ball (c p) r := by
    rw [← hBtarget]
    exact B.map_source (hBsource ▸ mem_univ z)
  let g : EuclideanSpace ℝ (Fin 2) → M := c.symm ∘ B
  have hg : Continuous g := c.continuousOn_symm.comp_continuous
    (OpenPartialHomeomorph.continuous_univBall _ _) (fun z => htarget (hBmem z))
  have hginj : Function.Injective g := by
    intro z w h
    apply B.injOn (hBsource ▸ mem_univ z) (hBsource ▸ mem_univ w)
    exact c.symm.injOn (htarget (hBmem z)) (htarget (hBmem w)) h
  have hpre : (g ⁻¹' V).Finite := hV.preimage hginj.injOn
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hconn := (hpre.countable.isConnected_compl_of_one_lt_rank hrank).isPreconnected.image
    g hg.continuousOn
  have himage : g '' (g ⁻¹' V)ᶜ = (c.symm '' ball (c p) r) \ V := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨B z, hBmem z, rfl⟩, hz⟩
    · rintro ⟨⟨z, hz, rfl⟩, hnot⟩
      obtain ⟨w, _, hw⟩ := B.surjOn (hBtarget.symm ▸ hz)
      refine ⟨w, ?_, ?_⟩
      · change c.symm (B w) ∉ V
        simpa only [hw] using hnot
      · simp only [g, Function.comp_apply, hw]
  rwa [himage] at hconn

variable [IsManifold (𝓡 2) ∞ M]

theorem SmoothEdge.exists_mem_neighborhood_not_mem_finite (e : SmoothEdge M)
    (hinj : InjOn e.map (Icc (0 : ℝ) 1))
    {p : M} (hp : p ∈ e.map '' Icc (0 : ℝ) 1)
    {N : Set M} (hN : IsOpen N) (hpN : p ∈ N)
    {V : Set M} (hV : V.Finite) :
    ∃ z ∈ N, z ∈ e.map '' Icc (0 : ℝ) 1 ∧ z ∉ V := by
  have hclosure : p ∈ closure (e.map '' Ioo (0 : ℝ) 1) :=
    ((e.image_Icc_subset_closed_iff isClosed_closure).mpr subset_closure) hp
  obtain ⟨z, hzN, t, ht, rfl⟩ := mem_closure_iff.mp hclosure N hN hpN
  have hnbhd : Ioo (0 : ℝ) 1 ∩ e.map ⁻¹' N ∈ 𝓝 t :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds ht)
      ((e.smooth.continuousOn.continuousAt (Icc_mem_nhds ht.1 ht.2)).preimage_mem_nhds
        (hN.mem_nhds hzN))
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnbhd
  have hinj' : InjOn e.map (Ioo a b) := hinj.mono
    (fun u hu => Ioo_subset_Icc_self (hsub hu).1)
  have hinfinite : (e.map '' Ioo a b).Infinite :=
    Set.Infinite.image hinj' (Ioo_infinite (hab.1.trans hab.2))
  obtain ⟨w, ⟨u, hu, rfl⟩, hw⟩ := Set.not_subset.mp (fun h => hinfinite (hV.subset h))
  exact ⟨e.map u, (hsub hu).2, ⟨u, Ioo_subset_Icc_self (hsub hu).1, rfl⟩, hw⟩

theorem frontier_edge_complement_subset_closure_sdiff_finite [T2Space M]
    {I : Type v} [Finite I] (edge : I → SmoothEdge M)
    (hinj : ∀ i, InjOn (edge i).map (Icc (0 : ℝ) 1))
    {V : Set M} (hV : V.Finite)
    (hVK : V ⊆ ⋃ i, (edge i).map '' Icc (0 : ℝ) 1) (x : M) :
    frontier (connectedComponentIn (⋃ i, (edge i).map '' Icc (0 : ℝ) 1)ᶜ x) ⊆
      closure (frontier (connectedComponentIn
        (⋃ i, (edge i).map '' Icc (0 : ℝ) 1)ᶜ x) \ V) := by
  have : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  let K : Set M := ⋃ i, (edge i).map '' Icc (0 : ℝ) 1
  let U := connectedComponentIn Kᶜ x
  have hKclosed : IsClosed K :=
    (isCompact_iUnion (fun i => isCompact_Icc.image_of_continuousOn
      (edge i).smooth.continuousOn)).isClosed
  have hUopen : IsOpen U := hKclosed.isOpen_compl.connectedComponentIn
  have hUsub : U ⊆ Kᶜ := connectedComponentIn_subset Kᶜ x
  have hfrontK : frontier U ⊆ K :=
    Poincare.Topology.frontier_connectedComponentIn_compl_subset hKclosed x
  intro p hp
  apply _root_.mem_closure_iff.mpr
  intro N hN hpN
  by_contra hnone
  have hfrontN : N ∩ frontier U ⊆ V := by
    intro y hy
    by_contra hyV
    exact hnone ⟨y, hy.1, hy.2, hyV⟩
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) p
  have hpc : p ∈ c.source := mem_chart_source _ p
  have hnbhd : c.target ∩ c.symm ⁻¹' N ∈ 𝓝 (c p) := by
    refine Filter.inter_mem (c.open_target.mem_nhds (c.map_source hpc)) ?_
    apply (c.continuousAt_symm (c.map_source hpc)).preimage_mem_nhds
    simpa only [c.left_inv hpc] using hN.mem_nhds hpN
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnbhd
  let D := c.symm '' ball (c p) r
  have htarget : ball (c p) r ⊆ c.target := fun _ hz => (hball hz).1
  have hDopen : IsOpen D := c.isOpen_image_symm_of_subset_target isOpen_ball htarget
  have hpD : p ∈ D := ⟨c p, mem_ball_self hr, c.left_inv hpc⟩
  have hDN : D ⊆ N := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hball hz).2
  have hDconn : IsPreconnected (D \ V) :=
    isPreconnected_chart_ball_sdiff_finite p hr htarget hV
  have hdisjoint : Disjoint (D \ V) (frontier U) := by
    apply disjoint_left.mpr
    intro z hz hzfront
    exact hz.2 (hfrontN ⟨hDN hz.1, hzfront⟩)
  obtain ⟨z, hzD, hzU⟩ :=
    mem_closure_iff.mp (frontier_subset_closure hp) D hDopen hpD
  have hinside : D \ V ⊆ U := by
    rw [← hUopen.interior_eq]
    apply Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier hDconn hdisjoint
    exact ⟨z, ⟨hzD, fun hzV => hUsub hzU (hVK hzV)⟩, hUopen.interior_eq.symm ▸ hzU⟩
  obtain ⟨i, hpi⟩ := mem_iUnion.mp (hfrontK hp)
  obtain ⟨w, hwD, hwi, hwV⟩ :=
    (edge i).exists_mem_neighborhood_not_mem_finite (hinj i) hpi hDopen hpD hV
  exact hUsub (hinside ⟨hwD, hwV⟩) (mem_iUnion.mpr ⟨i, hwi⟩)

theorem frontier_edge_complement_eq_iUnion_of_uniform_incidence [T2Space M]
    {I : Type v} [Finite I] (edge : I → SmoothEdge M)
    (hinj : ∀ i, InjOn (edge i).map (Icc (0 : ℝ) 1)) (x : M)
    (huniform : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1,
      (edge i).map t ∈ frontier (connectedComponentIn
        (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x) →
      (edge i).map '' Icc (0 : ℝ) 1 ⊆ frontier (connectedComponentIn
        (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x)) :
    frontier (connectedComponentIn (⋃ i, (edge i).map '' Icc (0 : ℝ) 1)ᶜ x) =
      ⋃ i : {i : I | (edge i).map '' Icc (0 : ℝ) 1 ⊆
        frontier (connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x)},
        (edge i).map '' Icc (0 : ℝ) 1 := by
  have : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  let K : Set M := ⋃ i, (edge i).map '' Icc (0 : ℝ) 1
  let U := connectedComponentIn Kᶜ x
  let V : Set M := ⋃ i, {(edge i).map 0, (edge i).map 1}
  have hV : V.Finite := finite_iUnion (fun i => (finite_singleton ((edge i).map 1)).insert _)
  have hVK : V ⊆ K := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    rcases hi with h | h
    · exact mem_iUnion.mpr ⟨i, 0, by simp, h.symm⟩
    · exact mem_iUnion.mpr ⟨i, 1, by simp, h.symm⟩
  let J := {i : I | (edge i).map '' Icc (0 : ℝ) 1 ⊆ frontier U}
  let B : Set M := ⋃ i : J, (edge i).map '' Icc (0 : ℝ) 1
  have hBclosed : IsClosed B := isClosed_iUnion_of_finite (fun i =>
    (isCompact_Icc.image_of_continuousOn (edge i).smooth.continuousOn).isClosed)
  have hKclosed : IsClosed K := isClosed_iUnion_of_finite (fun i =>
    (isCompact_Icc.image_of_continuousOn (edge i).smooth.continuousOn).isClosed)
  have hnonvertex : frontier U \ V ⊆ B := by
    intro z hz
    have hzK := Poincare.Topology.frontier_connectedComponentIn_compl_subset hKclosed x hz.1
    obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hzK
    have htzero : t ≠ 0 := by
      rintro rfl
      exact hz.2 (mem_iUnion.mpr ⟨i, Or.inl rfl⟩)
    have htone : t ≠ 1 := by
      rintro rfl
      exact hz.2 (mem_iUnion.mpr ⟨i, Or.inr rfl⟩)
    have htopen : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 htzero.symm, lt_of_le_of_ne ht.2 htone⟩
    exact mem_iUnion.mpr ⟨⟨i, huniform i t htopen hz.1⟩, ⟨t, ht, rfl⟩⟩
  apply Subset.antisymm
  · intro z hz
    have hdense := frontier_edge_complement_subset_closure_sdiff_finite edge hinj hV hVK x hz
    have h := closure_mono hnonvertex hdense
    simpa only [hBclosed.closure_eq] using h
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact i.property hi

theorem frontier_chartCircle_edge_complement_eq_iUnion [T2Space M]
    {I : Type v} [Finite I] (edge : I → SmoothEdge M) (p : I → M) (r : I → ℝ)
    (hinj : ∀ i, InjOn (edge i).map (Icc (0 : ℝ) 1))
    (hmeet : ∀ i j, j ≠ i →
      (edge i).map '' Icc (0 : ℝ) 1 ∩ (edge j).map '' Icc (0 : ℝ) 1 ⊆
        {(edge i).map 0, (edge i).map 1})
    (hpos : ∀ i, 0 < r i)
    (htarget : ∀ i, closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) (p i) (p i)) (r i) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).target)
    (hedge : ∀ i, (edge i).map '' Icc (0 : ℝ) 1 ⊆ chartCircle (p i) (r i))
    (hcircle : ∀ i, chartCircle (p i) (r i) ⊆ ⋃ j, (edge j).map '' Icc (0 : ℝ) 1)
    (x : M) :
    frontier (connectedComponentIn (⋃ i, (edge i).map '' Icc (0 : ℝ) 1)ᶜ x) =
      ⋃ i : {i : I | (edge i).map '' Icc (0 : ℝ) 1 ⊆
        frontier (connectedComponentIn (⋃ j, (edge j).map '' Icc (0 : ℝ) 1)ᶜ x)},
        (edge i).map '' Icc (0 : ℝ) 1 := by
  apply frontier_edge_complement_eq_iUnion_of_uniform_incidence edge hinj x
  intro i t ht hpoint
  have hsource : (edge i).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).source := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hedge i hz
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) (p i)).map_target
      (htarget i (sphere_subset_closedBall hw))
  obtain ⟨u, v, _, _, _, hiff⟩ :=
    exists_exactly_two_incident_components_along_chartCircle_edge edge i (p i) (p i)
      (hinj i) hsource
      (hmeet i) (hpos i) (htarget i) (hedge i) (hcircle i)
  have hincident := (hiff t ht x).mp hpoint
  rw [(edge i).image_Icc_subset_closed_iff isClosed_frontier]
  rintro z ⟨s, hs, rfl⟩
  exact (hiff s hs x).mpr hincident

end PoincareConjecture.Topology.Surface
