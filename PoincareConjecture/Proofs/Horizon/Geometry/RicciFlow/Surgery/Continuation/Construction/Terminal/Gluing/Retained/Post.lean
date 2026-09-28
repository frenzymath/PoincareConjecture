import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Caps.Boundary

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

def retainedPost : Set (cutCarrier I R U hU hd hc).carrier :=
  (⋃ i, interior (capChart I R U hU hd hc i).carrier)ᶜ

theorem retainedPost_closed : IsClosed (retainedPost I R U hU hd hc) :=
  (isOpen_iUnion (fun _ => isOpen_interior)).isClosed_compl

theorem retainedPost_compact [CompactSpace (cutCarrier I R U hU hd hc).carrier] :
    IsCompact (retainedPost I R U hU hd hc) :=
  (retainedPost_closed I R U hU hd hc).isCompact

theorem retainedPost_cover :
    retainedPost I R U hU hd hc ∪ ⋃ i, (capChart I R U hU hd hc i).carrier = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ retainedPost I R U hU hd hc
  · exact Or.inl hx
  · have hi : x ∈ ⋃ i, interior (capChart I R U hU hd hc i).carrier :=
      not_not.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hi
    exact Or.inr (mem_iUnion.mpr ⟨i, interior_subset hi⟩)

theorem retainedPost_inter_cap (i : ι) :
    retainedPost I R U hU hd hc ∩ (capChart I R U hU hd hc i).carrier =
      frontier (capChart I R U hU hd hc i).carrier := by
  rw [frontier, (capChart I R U hU hd hc i).carrier_compact.isClosed.closure_eq]
  ext x
  constructor
  · rintro ⟨hx, hxi⟩
    exact ⟨hxi, fun h => hx (mem_iUnion.mpr ⟨i, h⟩)⟩
  · rintro ⟨hxi, hnot⟩
    refine ⟨?_, hxi⟩
    intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    by_cases hij : i = j
    · exact hnot (hij ▸ hxj)
    · exact Set.disjoint_left.mp (capChart_disjoint I R U hU hd hc hij)
        hxi (interior_subset hxj)

theorem retainedPost_cap_boundary (i : ι) :
    retainedPost I R U hU hd hc ∩ (capChart I R U hU hd hc i).carrier =
      capInclusion I R U hU hd hc i '' ((R i).collapse '' (I i).neck.central_sphere) := by
  rw [retainedPost_inter_cap, capChart_frontier]

theorem retainedPost_interior_disjoint_cap (i : ι) :
    Disjoint (interior (retainedPost I R U hU hd hc)) (capChart I R U hU hd hc i).carrier := by
  rw [← capChart_closure_interior]
  apply Disjoint.closure_right _ isOpen_interior
  apply Set.disjoint_left.mpr
  intro x hx hi
  exact interior_subset hx (mem_iUnion.mpr ⟨i, hi⟩)

end PoincareConjecture.Surgery.Terminal.Gluing
