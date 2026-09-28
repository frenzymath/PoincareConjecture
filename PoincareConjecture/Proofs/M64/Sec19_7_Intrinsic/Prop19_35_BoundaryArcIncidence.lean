import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryArcTopology
import PoincareConjecture.Proofs.Horizon.Topology.Connected.ClosedCover

noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_real_boundary_two_sides
    {X : Type*} [TopologicalSpace X] (C : OpenPartialHomeomorph ℝ X)
    {p : X} (hp : p ∈ C.target) {N : Set X} (hN : N ∈ 𝓝 p) :
    ∃ W A B : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ N ∧
      W \ {p} = A ∪ B ∧ IsPreconnected A ∧ IsPreconnected B ∧
      A.Nonempty ∧ B.Nonempty ∧ p ∈ closure A ∧ p ∈ closure B ∧
      W ⊆ closure (A ∪ B) := by
  let x := C.symm p
  have hx : x ∈ C.source := C.map_target hp
  have hxp : C x = p := C.right_inv hp
  have hnear : C.source ∩ C ⁻¹' N ∈ 𝓝 x :=
    inter_mem (C.open_source.mem_nhds hx)
      ((C.continuousAt hx).preimage_mem_nhds (hxp.symm ▸ hN))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let d := r / 2
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdr : d < r := by dsimp only [d]; linarith
  have hlocal : Icc (x - d) (x + d) ⊆ C.source ∩ C ⁻¹' N := by
    intro t ht
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  let W := C '' Ioo (x - d) (x + d)
  let A := C '' Ioo (x - d) x
  let B := C '' Ioo x (x + d)
  have hleft : Icc (x - d) x ⊆ C.source := fun t ht =>
    (hlocal ⟨ht.1, ht.2.trans (by linarith)⟩).1
  have hright : Icc x (x + d) ⊆ C.source := fun t ht =>
    (hlocal ⟨(by linarith : x - d ≤ x).trans ht.1, ht.2⟩).1
  have hAclosure : p ∈ closure A := by
    have h := (show ContinuousOn C (closure (Ioo (x - d) x)) by
      rw [closure_Ioo (by linarith : x - d ≠ x)]
      exact C.continuousOn.mono hleft).image_closure
    apply h
    refine ⟨x, ?_, hxp⟩
    rw [closure_Ioo (by linarith : x - d ≠ x)]
    exact ⟨by linarith, le_rfl⟩
  have hBclosure : p ∈ closure B := by
    have h := (show ContinuousOn C (closure (Ioo x (x + d))) by
      rw [closure_Ioo (by linarith : x ≠ x + d)]
      exact C.continuousOn.mono hright).image_closure
    apply h
    refine ⟨x, ?_, hxp⟩
    rw [closure_Ioo (by linarith : x ≠ x + d)]
    exact ⟨le_rfl, by linarith⟩
  have hpartition : W \ {p} = A ∪ B := by
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hne⟩
      have htx : t ≠ x := by
        intro h
        exact hne (by simp only [h, hxp, mem_singleton_iff])
      rcases lt_or_gt_of_ne htx with h | h
      · exact Or.inl ⟨t, ⟨ht.1, h⟩, rfl⟩
      · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · refine ⟨⟨t, ⟨ht.1, ht.2.trans (by linarith)⟩, rfl⟩, ?_⟩
        intro heq
        have heq' : C t = C x := (mem_singleton_iff.mp heq).trans hxp.symm
        exact ht.2.ne (C.injOn (hleft (Ioo_subset_Icc_self ht)) hx heq')
      · refine ⟨⟨t, ⟨(by linarith : x - d < x).trans ht.1, ht.2⟩, rfl⟩, ?_⟩
        intro heq
        have heq' : C t = C x := (mem_singleton_iff.mp heq).trans hxp.symm
        exact ht.1.ne' (C.injOn (hright (Ioo_subset_Icc_self ht)) hx heq')
  refine ⟨W, A, B,
    C.isOpen_image_of_subset_source isOpen_Ioo
      (fun t ht => (hlocal (Ioo_subset_Icc_self ht)).1),
    ⟨x, ⟨by linarith, by linarith⟩, hxp⟩, ?_, hpartition,
    isPreconnected_Ioo.image C (C.continuousOn.mono (Ioo_subset_Icc_self.trans hleft)),
    isPreconnected_Ioo.image C (C.continuousOn.mono (Ioo_subset_Icc_self.trans hright)),
    (nonempty_Ioo.mpr (by linarith : x - d < x)).image C,
    (nonempty_Ioo.mpr (by linarith : x < x + d)).image C,
    hAclosure, hBclosure, ?_⟩
  · rintro z ⟨t, ht, rfl⟩
    exact (hlocal (Ioo_subset_Icc_self ht)).2
  · intro z hz
    by_cases hzp : z = p
    · subst z
      exact closure_mono subset_union_left hAclosure
    · exact subset_closure (hpartition ▸ ⟨hz, hzp⟩)

theorem m64Intrinsic_real_boundary_closed_cover_incidence
    {X I : Type*} [TopologicalSpace X] [T2Space X] [Finite I]
    (hcharts : ∀ x : X, ∃ C : OpenPartialHomeomorph ℝ X, x ∈ C.target)
    (A : I → Set X) (hclosed : ∀ i, IsClosed (A i))
    (hregular : ∀ i, closure (interior (A i)) = A i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (A i)) (interior (A j))))
    (hcover : (⋃ i, A i) = univ) (hfinite : (⋃ i, frontier (A i)).Finite)
    {p : X} (hp : ∃ i, p ∈ frontier (A i)) :
    ∃ i j : I, i ≠ j ∧ ∀ k, p ∈ A k ↔ k = i ∨ k = j := by
  let K := ⋃ i, frontier (A i)
  have hK : (K \ {p}).Finite := hfinite.sdiff
  have hN : (K \ {p})ᶜ ∈ 𝓝 p :=
    hK.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨C, hC⟩ := hcharts p
  obtain ⟨W, U, V, hW, hpW, hWN, hpartition, hU, hV, hUne, hVne, hpU, hpV, hdense⟩ :=
    m64Intrinsic_real_boundary_two_sides C hC hN
  have hfront : ∀ i, W ∩ frontier (A i) ⊆ {p} := by
    intro i z hz
    by_contra hzp
    exact hWN hz.1 ⟨mem_iUnion.mpr ⟨i, hz.2⟩, hzp⟩
  obtain ⟨i, j, hij, _, _, hmembers⟩ :=
    Poincare.Topology.exists_exactly_two_closed_cover_members_of_two_sided_neighborhood
      A hclosed hregular hdisjoint hcover (hW.mem_nhds hpW) hpartition
      hU hV hUne hVne hpU hpV hdense hfront hp
  exact ⟨i, j, hij, hmembers⟩

theorem m64Intrinsic_exactly_two_boundary_arcs
    {X I : Type*} [TopologicalSpace X] [T2Space X] [Finite I]
    (hcharts : ∀ x : X, ∃ C : OpenPartialHomeomorph ℝ X, x ∈ C.target)
    (f : I → ℝ → X) (hc : ∀ i, ContinuousOn (f i) (Icc 0 1))
    (hinj : ∀ i, InjOn (f i) (Icc 0 1))
    (hmeet : ∀ i j, i ≠ j → f i '' Icc 0 1 ∩ f j '' Icc 0 1 ⊆ {f i 0, f i 1})
    (hcover : (⋃ i, f i '' Icc 0 1) = univ)
    {p : X} (hp : ∃ i, p = f i 0 ∨ p = f i 1) :
    ∃ i j : I, i ≠ j ∧ ∀ k, p ∈ f k '' Icc 0 1 ↔ k = i ∨ k = j := by
  have hregular (i : I) := m64Intrinsic_arc_regular_closed_in_real_boundary
    hcharts (by norm_num : (0 : ℝ) < 1) (hc i) (hinj i)
  have hfront (i : I) := m64Intrinsic_arc_frontier_eq_endpoints
    hcharts (by norm_num : (0 : ℝ) < 1) (hc i) (hinj i)
  apply m64Intrinsic_real_boundary_closed_cover_incidence hcharts
    (fun i => f i '' Icc 0 1) (fun i => (hregular i).1)
    (fun i => (hregular i).2.1) ?_ hcover ?_ ?_
  · intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    have h : x ∈ frontier (f i '' Icc 0 1) :=
      (hfront i).symm ▸ hmeet i j hij ⟨interior_subset hxi, interior_subset hxj⟩
    exact h.2 hxi
  · simp_rw [hfront]
    exact finite_iUnion (fun i => (finite_singleton (f i 1)).insert (f i 0))
  · obtain ⟨i, hi⟩ := hp
    exact ⟨i, (hfront i).symm ▸ hi⟩

end PoincareConjecture
