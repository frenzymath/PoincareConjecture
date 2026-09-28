import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.PuncturedPieces

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

def cutTips : Set (cutCarrier I R U hU hd hc).carrier :=
  range (fun i => capInclusion I R U hU hd hc i (R i).tip)

theorem cutTips_finite [Finite ι] : (cutTips I R U hU hd hc).Finite := finite_range _

theorem retainedInclusion_notMem_cutTips (x : U) :
    retainedInclusion I R U hU hd hc x ∉ cutTips I R U hU hd hc := by
  rintro ⟨i, hi⟩
  have hx := (retainedInclusion_mem_cap_iff I R U hU hd hc i x).mp ⟨(R i).tip, hi⟩
  have he : (R i).collapse x.val = (R i).tip :=
    (capInclusion_openEmbedding I R U hU hd hc i).injective
      ((retainedInclusion_eq_cap I R U hU hd hc i x hx).symm.trans hi.symm)
  exact (R i).collapse_negative_ne_tip hx he

theorem capInclusion_mem_cutTips_iff (i : ι) (x : (R i).output.carrier) :
    capInclusion I R U hU hd hc i x ∈ cutTips I R U hU hd hc ↔ x = (R i).tip := by
  constructor
  · rintro ⟨j, hj⟩
    by_cases hij : i = j
    · subst j
      exact ((capInclusion_openEmbedding I R U hU hd hc i).injective hj).symm
    · exact False.elim (Set.disjoint_left.mp (capInclusion_disjoint I R U hU hd hc hij)
        ⟨x, rfl⟩ ⟨(R j).tip, hj⟩)
  · rintro rfl
    exact mem_range_self i

theorem puncturedInclusion_iUnion_range :
    (⋃ j, range (puncturedInclusion I R U hU hd hc j)) = (cutTips I R U hU hd hc)ᶜ := by
  ext q
  constructor
  · intro hq
    obtain ⟨j, x, rfl⟩ := mem_iUnion.mp hq
    cases j with
    | none => exact retainedInclusion_notMem_cutTips I R U hU hd hc x
    | some i =>
      intro hx
      exact x.property ((capInclusion_mem_cutTips_iff I R U hU hd hc i x.val).mp hx)
  · intro hq
    rcases cutCarrier_cover I R U hU hd hc q with ⟨x, rfl⟩ | ⟨i, x, rfl⟩
    · exact mem_iUnion.mpr ⟨none, x, rfl⟩
    · have hx : x ≠ (R i).tip := fun he =>
        hq ((capInclusion_mem_cutTips_iff I R U hU hd hc i x).mpr he)
      exact mem_iUnion.mpr ⟨some i, ⟨x, hx⟩, rfl⟩

end PoincareConjecture.Surgery.Terminal.Gluing
