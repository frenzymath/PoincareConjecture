import PoincareConjecture.Definitions.Ch19.AnnulusComparison
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Incidence











noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture




def m64Intrinsic_cappedRegionCarrier {I : Type*}
    (face : I → SmoothFace AnnulusCoordinates) (V : Set AnnulusCoordinates) :
    Sum I Unit → Set AnnulusCoordinates :=
  Sum.elim (fun i => (face i).carrier) (fun _ => closure V)




theorem m64Intrinsic_capped_region_cover
    {I : Type*} [Finite I] (face : I → SmoothFace AnnulusCoordinates)
    (C : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (C i).source)
    (hcarrier : ∀ i, (face i).carrier = C i '' convexHull ℝ (range (b i)))
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfrontier : frontier U = frontier V)
    (hclosure : closure U ∪ closure V = univ)
    (hregion : (⋃ i, (face i).carrier) = closure U) :
    (∀ a, IsClosed (m64Intrinsic_cappedRegionCarrier face V a)) ∧
      (∀ a, closure (interior (m64Intrinsic_cappedRegionCarrier face V a)) =
        m64Intrinsic_cappedRegionCarrier face V a) ∧
      Pairwise (fun a d => Disjoint
        (interior (m64Intrinsic_cappedRegionCarrier face V a))
        (interior (m64Intrinsic_cappedRegionCarrier face V d))) ∧
      (⋃ a, m64Intrinsic_cappedRegionCarrier face V a) = univ ∧
      (⋃ a, frontier (m64Intrinsic_cappedRegionCarrier face V a)) =
        ⋃ i, frontier (face i).carrier := by
  let A := m64Intrinsic_cappedRegionCarrier face V
  have hfaceU (i : I) : (face i).carrier ⊆ closure U := by
    rw [← hregion]
    exact subset_iUnion (fun j => (face j).carrier) i
  have hUCV : Disjoint (closure U) (interior (closure V)) :=
    ((hdisj.closure_right hU).mono_right interior_subset).closure_left isOpen_interior
  have hUICV : Disjoint (interior (closure U)) (closure V) :=
    ((hdisj.closure_left hV).mono_left interior_subset).closure_right isOpen_interior
  have hclosed (a : Sum I Unit) : IsClosed (A a) := by
    cases a with
    | inl i => exact (face i).isClosed_carrier
    | inr u => exact isClosed_closure
  have hregular (a : Sum I Unit) : closure (interior (A a)) = A a := by
    cases a with
    | inl i =>
      change closure (interior (face i).carrier) = (face i).carrier
      rw [hcarrier]
      exact coordinate_triangle_closure_interior (C i) (b i) (hsource i)
    | inr u =>
      change closure (interior (closure V)) = closure V
      exact subset_antisymm (closure_minimal interior_subset isClosed_closure)
        (closure_mono hV.subset_interior_closure)
  have hdisjoint : Pairwise (fun a d => Disjoint (interior (A a)) (interior (A d))) := by
    intro a d had
    cases a with
    | inl i =>
      cases d with
      | inl j =>
        exact (face i).disjoint_interiors_of_inter_subset_frontier (face j)
          (hfront i j (fun hij => had (congrArg Sum.inl hij)))
      | inr u => exact hUCV.mono_left (interior_subset.trans (hfaceU i))
    | inr u =>
      cases d with
      | inl j => exact hUCV.symm.mono_right (interior_subset.trans (hfaceU j))
      | inr v => exact (had (by cases u; cases v; rfl)).elim
  have hcover : (⋃ a, A a) = univ := by
    apply eq_univ_of_forall
    intro p
    rcases (show p ∈ closure U ∪ closure V from hclosure.symm ▸ mem_univ p) with hp | hp
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hregion.symm ▸ hp)
      exact mem_iUnion.mpr ⟨Sum.inl i, hi⟩
    · exact mem_iUnion.mpr ⟨Sum.inr (), hp⟩
  refine ⟨hclosed, hregular, hdisjoint, hcover, ?_⟩
  apply subset_antisymm
  · intro p hp
    obtain ⟨a, ha⟩ := mem_iUnion.mp hp
    cases a with
    | inl i => exact mem_iUnion.mpr ⟨i, ha⟩
    | inr u =>
      change p ∈ frontier (closure V) at ha
      have hpV : p ∈ closure V := isClosed_closure.frontier_subset ha
      have hpU : p ∈ frontier U := hfrontier.symm ▸ frontier_closure_subset ha
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hregion.symm ▸ hpU.1)
      refine mem_iUnion.mpr ⟨i, subset_closure hi, ?_⟩
      intro hint
      exact disjoint_left.mp hUICV (interior_mono (hfaceU i) hint) hpV
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨Sum.inl i, hi⟩




theorem m64Intrinsic_exists_capped_region_adjacent_faces
    {I : Type*} [Finite I] (face : I → SmoothFace AnnulusCoordinates)
    (C : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (C i).source)
    (hcarrier : ∀ i, (face i).carrier = C i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = C i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ v : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {C i (b i v)})
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfrontier : frontier U = frontier V)
    (hclosure : closure U ∪ closure V = univ)
    (hregion : (⋃ i, (face i).carrier) = closure U) :
    ∃ adjacent : FaceBoundaryEdge face → (Sum I Unit) × (Sum I Unit),
      (∀ e, (adjacent e).1 ≠ (adjacent e).2) ∧
      ∀ e a, (faceBoundaryEdge face e).map (1 / 2 : ℝ) ∈
        m64Intrinsic_cappedRegionCarrier face V a ↔
          a = (adjacent e).1 ∨ a = (adjacent e).2 := by
  classical
  let A := m64Intrinsic_cappedRegionCarrier face V
  let K := ⋃ e, (faceBoundaryEdge face e).map '' Icc (0 : ℝ) 1
  let _ := Fintype.ofFinite (Sum I Unit)
  obtain ⟨hclosed, hregular, hdisjoint, hcover, hfrontiers⟩ :=
    m64Intrinsic_capped_region_cover face C b hsource hcarrier hfront hU hV hdisj
      hfrontier hclosure hregion
  have hinj (i : I) (k : Fin 3) : InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1) := by
    have hne : b i (k.succAbove 1) - b i (k.succAbove 0) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      have h := Fin.succAbove_right_injective (p := k) ((b i).ind.injective heq)
      norm_num at h
    have hseg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
        affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)) t ∈ (C i).source :=
      hsource i (Euler.coordinate_edge_subset_hull (b i) k
        (Euler.affineChartSegment_image _ _ ▸ mem_image_of_mem _ ht))
    intro t ht s hs heq
    rw [hboundary] at heq
    exact smul_left_injective ℝ hne (add_left_cancel ((C i).injOn (hseg ht) (hseg hs) heq))
  have hmeet (e d : FaceBoundaryEdge face) (hed : e ≠ d) :
      (faceBoundaryEdge face e).map '' Icc (0 : ℝ) 1 ∩
        (faceBoundaryEdge face d).map '' Icc (0 : ℝ) 1 ⊆
      {(faceBoundaryEdge face e).map 0, (faceBoundaryEdge face e).map 1} := by
    apply Euler.coordinate_cover_edge_meet face C b hsource hboundary hinj hinter
      e.out.1 d.out.1 e.out.2 d.out.2
    intro heq
    apply hed
    have h := (faceBoundaryIndex_eq_iff face e.out.1 d.out.1 e.out.2 d.out.2).mpr heq
    exact (Quotient.out_eq e).symm.trans (h.trans (Quotient.out_eq d))
  have hK : K = ⋃ a, frontier (A a) := by
    rw [hfrontiers]
    apply subset_antisymm
    · intro p hp
      obtain ⟨e, he⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨e.out.1, (face e.out.1).boundary_image_subset_frontier e.out.2 he⟩
    · intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      rw [(face i).boundary_carrier] at hi
      obtain ⟨k, hk⟩ := mem_iUnion.mp hi
      apply mem_iUnion.mpr
      refine ⟨faceBoundaryIndex face i k, ?_⟩
      rw [faceBoundaryEdge_image]
      exact hk
  have hdense : Dense Kᶜ := by
    rw [hK]
    simpa only [Finset.mem_univ, iUnion_true] using
      Poincare.Topology.dense_compl_finite_frontier_union Finset.univ A
        (fun a _ => hclosed a)
  have heach (e : FaceBoundaryEdge face) : ∃ a d : Sum I Unit, a ≠ d ∧
      ∀ f, (faceBoundaryEdge face e).map (1 / 2 : ℝ) ∈ A f ↔ f = a ∨ f = d := by
    let q := (faceBoundaryEdge face e).map (1 / 2 : ℝ)
    have ht : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
    have hedgefront : (faceBoundaryEdge face e).map '' Icc (0 : ℝ) 1 ⊆
        frontier (face e.out.1).carrier :=
      (face e.out.1).boundary_image_subset_frontier e.out.2
    have hedgechart : (faceBoundaryEdge face e).map '' Icc (0 : ℝ) 1 ⊆
        (chartAt AnnulusCoordinates (face e.out.1).chart).source :=
      hedgefront.trans ((face e.out.1).isClosed_carrier.frontier_subset.trans
        (face e.out.1).carrier_subset_chart)
    have hqfront : q ∈ frontier (face e.out.1).carrier :=
      hedgefront ⟨1 / 2, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    obtain ⟨W, L, R, hW, hqW, _, _, _, hL, hR, _, hpartition, hqLR⟩ :=
      exists_two_sided_edge_family_neighborhood_of_endpoint_intersections
        (faceBoundaryEdge face) e (face e.out.1).chart (hinj e.out.1 e.out.2)
        hedgechart (fun d hde => hmeet e d hde.symm) ht (s := univ) Filter.univ_mem
    have hWdense : W ⊆ closure (L ∪ R) := by
      rw [← hpartition]
      intro z hz
      apply mem_closure_iff.mpr
      intro O hO hzO
      obtain ⟨w, ⟨hwO, hwW⟩, hwK⟩ :=
        hdense.inter_open_nonempty (O ∩ W) (hO.inter hW) ⟨z, hzO, hz⟩
      exact ⟨w, hwO, hwW, hwK⟩
    have hlocal (a : Sum I Unit) : W ∩ frontier (A a) ⊆ K := by
      intro z hz
      rw [hK]
      exact mem_iUnion.mpr ⟨a, hz.2⟩
    obtain ⟨a, d, had, _, _, hmembers⟩ :=
      Poincare.Topology.exists_exactly_two_closed_cover_members_of_two_sided_neighborhood
        A hclosed hregular hdisjoint hcover (hW.mem_nhds hqW) hpartition
        hL.isConnected.isPreconnected hR.isConnected.isPreconnected hL.nonempty hR.nonempty
        hqLR.1 hqLR.2 hWdense hlocal ⟨Sum.inl e.out.1, hqfront⟩
    exact ⟨a, d, had, hmembers⟩
  choose left right hdistinct hexact using heach
  exact ⟨fun e => (left e, right e), hdistinct, hexact⟩




theorem m64Intrinsic_capped_region_interiors
    {I : Type*} (face : I → SmoothFace AnnulusCoordinates)
    (C : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (C i).source)
    (hcarrier : ∀ i, (face i).carrier = C i '' convexHull ℝ (range (b i)))
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfrontier : frontier U = frontier V)
    (hregion : (⋃ i, (face i).carrier) = closure U) (hVconn : IsPreconnected V) :
    ∀ a, IsPreconnected (interior (m64Intrinsic_cappedRegionCarrier face V a)) ∧
      Disjoint (interior (m64Intrinsic_cappedRegionCarrier face V a))
        (⋃ e : FaceBoundaryEdge face, (faceBoundaryEdge face e).map '' Icc (0 : ℝ) 1) := by
  let A := m64Intrinsic_cappedRegionCarrier face V
  have hfaceU (i : I) : (face i).carrier ⊆ closure U := by
    rw [← hregion]
    exact subset_iUnion (fun j => (face j).carrier) i
  have hUCV : Disjoint (closure U) (interior (closure V)) :=
    ((hdisj.closure_right hU).mono_right interior_subset).closure_left isOpen_interior
  have hVint : interior (closure V) = V := by
    apply subset_antisymm ?_ hV.subset_interior_closure
    intro p hp
    by_contra hpV
    have hpf : p ∈ frontier V :=
      ⟨interior_subset hp, by simpa only [hV.interior_eq] using hpV⟩
    have hpU : p ∈ closure U := (hfrontier.symm ▸ hpf).1
    exact disjoint_left.mp hUCV hpU hp
  have hconn (a : Sum I Unit) : IsPreconnected (interior (A a)) := by
    cases a with
    | inl i =>
      change IsPreconnected (interior (face i).carrier)
      rw [hcarrier, interior_smooth_coordinate_image (C i) (hsource i)]
      exact (convex_convexHull ℝ (range (b i))).interior.isPreconnected.image (C i)
        ((C i).continuousOn.mono (interior_subset.trans (hsource i)))
    | inr u =>
      change IsPreconnected (interior (closure V))
      rwa [hVint]
  have havoid (a : Sum I Unit) :
      Disjoint (interior (A a)) (⋃ i, frontier (face i).carrier) := by
    apply disjoint_left.mpr
    intro p hp hf
    obtain ⟨i, hi⟩ := mem_iUnion.mp hf
    cases a with
    | inl j =>
      by_cases hji : j = i
      · subst j
        exact hi.2 hp
      · exact (hfront j i hji ⟨interior_subset hp,
          (face i).isClosed_carrier.frontier_subset hi⟩).2 hp
    | inr u =>
      exact disjoint_left.mp hUCV
        (hfaceU i ((face i).isClosed_carrier.frontier_subset hi)) hp
  intro a
  refine ⟨hconn a, (havoid a).mono_right ?_⟩
  intro p hp
  obtain ⟨e, he⟩ := mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨e.out.1, (face e.out.1).boundary_image_subset_frontier e.out.2 he⟩

end PoincareConjecture
