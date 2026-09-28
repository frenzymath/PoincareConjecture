import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Compactness.Local










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Finite ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

theorem cutCarrier_compact
    (hcompact : IsCompact (closure (U : Set S.carrier)))
    (hboundary : frontier (U : Set S.carrier) ⊆ ⋃ i, (I i).neck.central_sphere)
    (hnegative : ∀ i, ((I i).negativeHalf : Set S.carrier) ⊆ U)
    (hside : ∀ i, (U : Set S.carrier) ∩ (I i).neck.region (-1) 1 ⊆ (I i).negativeHalf) :
    CompactSpace (cutCarrier I R U hU hd hc).carrier := by
  let band : Set S.carrier := ⋃ i, (I i).neck.region (-1) 1
  let A : Set S.carrier := closure (U : Set S.carrier) \ band
  have hband : IsOpen band := isOpen_iUnion (fun i => (I i).neck.isOpen_region (-1) 1)
  have hA : IsCompact A := hcompact.inter_right hband.isClosed_compl
  have hAU : A ⊆ U := by
    intro x hx
    by_contra hxu
    have hfront : x ∈ frontier (U : Set S.carrier) :=
      ⟨hx.1, by simpa only [U.isOpen.interior_eq] using hxu⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hboundary hfront)
    exact hx.2 (mem_iUnion.mpr ⟨i, (I i).neck.centralSphere_subset_band hi⟩)
  let A' : Set U := Subtype.val ⁻¹' A
  have hA' : IsCompact A' := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    hA (fun x hx => ⟨⟨x, hAU hx⟩, rfl⟩)
  let Q := (cutCarrier I R U hU hd hc).carrier
  let A₀ : Set Q := retainedInclusion I R U hU hd hc '' A'
  let B : ι → Set Q := fun i => capInclusion I R U hU hd hc i ''
    ((R i).collapse '' (I i).neck.centralClosedCollar ∪
      closure ((R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)))
  have hA₀ : IsCompact A₀ := hA'.image (retainedInclusion_openEmbedding I R U hU hd hc).continuous
  have hB (i : ι) : IsCompact (B i) :=
    ((R i).isCompact_collapse_centralCollar.union (R i).isCompact_closed_cap).image
      (capInclusion_openEmbedding I R U hU hd hc i).continuous
  have hbase (x : U) : retainedInclusion I R U hU hd hc x ∈ A₀ ∪ ⋃ i, B i := by
    by_cases hx : x.val ∈ band
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      have hxneg : x.val ∈ (I i).negativeHalf := hside i ⟨x.property, hxi⟩
      rw [retainedInclusion_eq_cap I R U hU hd hc i x hxneg]
      exact Or.inr (mem_iUnion.mpr ⟨i,
        mem_image_of_mem _ (Or.inl (mem_image_of_mem _
          ((I i).neck.centralBand_subset_closedCollar hxi)))⟩)
    · exact Or.inl ⟨x, ⟨subset_closure x.property, hx⟩, rfl⟩
  have hcover : (univ : Set Q) ⊆ A₀ ∪ ⋃ i, B i := by
    intro q _
    rcases cutCarrier_cover I R U hU hd hc q with ⟨x, rfl⟩ | ⟨i, y, rfl⟩
    · exact hbase x
    · have hy : y ∈ (R i).collapse '' ((I i).negativeHalf : Set S.carrier) ∪
          closure ((R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := by
        exact Set.eq_univ_iff_forall.mp (R i).output_cover y
      rcases hy with ⟨x, hx, rfl⟩ | hy
      · exact (retainedInclusion_eq_cap I R U hU hd hc i ⟨x, hnegative i hx⟩ hx) ▸
          hbase ⟨x, hnegative i hx⟩
      · exact Or.inr (mem_iUnion.mpr ⟨i, mem_image_of_mem _ (Or.inr hy)⟩)
  exact isCompact_univ_iff.mp
    ((hA₀.union (isCompact_iUnion hB)).of_isClosed_subset isClosed_univ hcover)

end PoincareConjecture.Surgery.Terminal.Gluing
