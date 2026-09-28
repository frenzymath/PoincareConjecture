import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Retained.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Retained.Post







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.MetricSurgeryResult

variable {S : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 S.carrier}
  {K : MetricSurgeryConstants} {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

include R in
theorem central_subset_closure_negative :
    I.neck.central_sphere ⊆ closure (I.negativeHalf : Set S.carrier) := by
  intro x hx
  have hy : R.collapse x ∈ closure (R.collapse '' (I.negativeHalf : Set S.carrier)) := by
    change R.collapse x ∈ closure (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 0)
    rw [← R.cap_exterior]
    apply frontier_subset_closure
    rw [frontier_compl, R.frontier_closed_cap]
    exact mem_image_of_mem _ hx
  have h := mem_closure_image (R.retained_inverse_continuousAt_closure_negative hy) hy
  have hsub : R.retained_inverse ''
      (R.collapse '' (I.negativeHalf : Set S.carrier)) ⊆ I.negativeHalf := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rwa [R.retained_left_inverse (I.negativeHalf_subset_retainedCollar hz)]
  have h' := closure_mono hsub h
  rwa [R.retained_left_inverse (I.centralSphere_subset_retainedCollar hx)] at h'

end PoincareConjecture.MetricSurgeryResult

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)
  (hneck : Pairwise (fun i j => Disjoint (I i).neck.carrier (I j).neck.carrier))
  (hUn : ∀ i, (U : Set S.carrier) ∩ (I i).neck.carrier = (I i).negativeHalf)

include R hUn in
omit [Countable ι] in
theorem centralSphere_subset_closure_retained (i : ι) :
    (I i).neck.central_sphere ⊆ closure (U : Set S.carrier) := by
  apply (R i).central_subset_closure_negative.trans
  apply closure_mono
  rw [← hUn i]
  exact inter_subset_left

theorem retainedInclusion_disjoint_cap (i : ι) :
    Disjoint (range (retainedInclusion I R U hU hd hc))
      (capChart I R U hU hd hc i).carrier := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, rfl⟩ ⟨z, hz, heq⟩
  have hx := (retainedInclusion_mem_cap_iff I R U hU hd hc i x).mp ⟨z, heq⟩
  have hzx : z = (R i).collapse x.val :=
    (capInclusion_openEmbedding I R U hU hd hc i).injective
      (heq.trans (retainedInclusion_eq_cap I R U hU hd hc i x hx))
  have hout : (R i).collapse x.val ∉
      closure ((R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := by
    change (R i).collapse x.val ∈
      (closure ((R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)))ᶜ
    rw [(R i).cap_exterior]
    exact mem_image_of_mem _ hx
  exact hout (hzx ▸ hz)

theorem retainedInclusion_subset_retainedPost :
    range (retainedInclusion I R U hU hd hc) ⊆ retainedPost I R U hU hd hc := by
  intro x hx hnot
  obtain ⟨i, hi⟩ := mem_iUnion.mp hnot
  exact Set.disjoint_left.mp (retainedInclusion_disjoint_cap I R U hU hd hc i)
    hx (interior_subset hi)

include hUn in
theorem retainedPost_decomposition : retainedPost I R U hU hd hc =
    range (retainedInclusion I R U hU hd hc) ∪
      ⋃ i, capInclusion I R U hU hd hc i '' ((R i).collapse '' (I i).neck.central_sphere) := by
  apply Subset.antisymm
  · intro y hy
    rcases cutCarrier_cover I R U hU hd hc y with hyU | ⟨i, z, rfl⟩
    · exact Or.inl hyU
    · have hz := Set.eq_univ_iff_forall.mp (R i).output_cover z
      rcases hz with ⟨x, hx, rfl⟩ | hz
      · have hxU : x ∈ U := by
          have hn : x ∈ (U : Set S.carrier) ∩ (I i).neck.carrier := (hUn i).symm ▸ hx
          exact hn.1
        exact Or.inl ⟨⟨x, hxU⟩, retainedInclusion_eq_cap I R U hU hd hc i ⟨x, hxU⟩ hx⟩
      · exact Or.inr (mem_iUnion.mpr ⟨i,
          (retainedPost_cap_boundary I R U hU hd hc i).subset
            ⟨hy, mem_image_of_mem _ hz⟩⟩)
  · rintro y (hy | hy)
    · exact retainedInclusion_subset_retainedPost I R U hU hd hc hy
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact ((retainedPost_cap_boundary I R U hU hd hc i).superset hi).1

variable (hfront : frontier (U : Set S.carrier) ⊆ ⋃ i, (I i).neck.central_sphere)

include hneck hUn hfront in
theorem retainedMap_image_eq_retainedPost :
    retainedMap I R U hU hd hc '' closure (U : Set S.carrier) =
      retainedPost I R U hU hd hc := by
  rw [retainedPost_decomposition I R U hU hd hc hUn]
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨⟨x, hxU⟩, (retainedMap_apply_retained I R U hU hd hc hneck hUn ⟨x, hxU⟩).symm⟩
    · have hxf : x ∈ frontier (U : Set S.carrier) := by
        rw [frontier, U.isOpen.interior_eq]
        exact ⟨hx, hxU⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront hxf)
      exact Or.inr (mem_iUnion.mpr ⟨i, (R i).collapse x, mem_image_of_mem _ hi,
        (retainedMap_apply_collar I R U hU hd hc hneck hUn i x
          ((I i).centralSphere_subset_retainedCollar hi)).symm⟩)
  · rintro y (⟨x, rfl⟩ | hy)
    · exact ⟨x.val, subset_closure x.property,
        retainedMap_apply_retained I R U hU hd hc hneck hUn x⟩
    · obtain ⟨i, _, ⟨x, hx, rfl⟩, rfl⟩ := mem_iUnion.mp hy
      exact ⟨x, centralSphere_subset_closure_retained I R U hUn i hx,
        retainedMap_apply_collar I R U hU hd hc hneck hUn i x
          ((I i).centralSphere_subset_retainedCollar hx)⟩

include R hU hd hc hneck hUn hfront in
theorem interior_closure_retained : interior (closure (U : Set S.carrier)) = U := by
  refine Subset.antisymm ?_ (interior_maximal subset_closure U.isOpen)
  intro x hx
  by_contra hxU
  have hxf : x ∈ frontier (U : Set S.carrier) := by
    rw [frontier, U.isOpen.interior_eq]
    exact ⟨interior_subset hx, hxU⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront hxf)
  have hmap := (retainedRegionEquivalence I R U hU hd hc hneck hUn hfront).mapsTo_interior hx
  change retainedMap I R U hU hd hc x ∈
    interior (retainedMap I R U hU hd hc '' closure (U : Set S.carrier)) at hmap
  rw [retainedMap_image_eq_retainedPost I R U hU hd hc hneck hUn hfront] at hmap
  have hcap : retainedMap I R U hU hd hc x ∈ (capChart I R U hU hd hc i).carrier := by
    apply frontier_subset_closure.trans (capChart I R U hU hd hc i).carrier_compact.isClosed.closure_subset
    rw [capChart_frontier, retainedMap_apply_collar I R U hU hd hc hneck hUn i x
      ((I i).centralSphere_subset_retainedCollar hi)]
    exact mem_image_of_mem _ (mem_image_of_mem _ hi)
  exact Set.disjoint_left.mp (retainedPost_interior_disjoint_cap I R U hU hd hc i) hmap hcap

include R hU hd hc hneck hUn hfront in
theorem frontier_closure_retained : frontier (closure (U : Set S.carrier)) =
    ⋃ i, (I i).neck.central_sphere := by
  rw [frontier, closure_closure, interior_closure_retained I R U hU hd hc hneck hUn hfront]
  refine Subset.antisymm ?_ ?_
  · intro x hx
    apply hfront
    rwa [frontier, U.isOpen.interior_eq]
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨centralSphere_subset_closure_retained I R U hUn i hi,
      fun hxU => Set.disjoint_left.mp (hc i) hxU hi⟩

end PoincareConjecture.Surgery.Terminal.Gluing
