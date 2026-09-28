import PoincareConjecture.Proofs.M54.ConnectedSum.Factors










set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture

namespace SmoothDisjointUnionData



noncomputable def inclusionGroupEquiv {n : ℕ}
    {pieces : Fin n → GeneralizedSliceCarrier.{u}} {C : GeneralizedSliceCarrier.{u}}
    (D : SmoothDisjointUnionData pieces C) (i : Fin n) (x : (pieces i).carrier) :
    FundamentalGroup (pieces i).carrier x ≃* FundamentalGroup C.carrier ((D.identify i).map x) := by
  let e := (Homeomorph.Set.univ (pieces i).carrier).symm.trans (D.identify i).toHomeomorph
  exact (e.fundamentalGroupMulEquiv x).trans
    ((show IsClopen (D.region i) from ⟨D.region_closed i, D.region_open i⟩).fundamentalGroupMulEquiv
      (e x))

end SmoothDisjointUnionData

namespace SmoothConnectedSumStep



theorem factor {A C : GeneralizedSliceCarrier.{u}} (h : SmoothConnectedSumStep A C)
    (x : A.carrier) :
    ∃ y : C.carrier,
      Nonempty (RepairedGroupFactorData (FundamentalGroup C.carrier y)
        (FundamentalGroup A.carrier x)) := by
  obtain ⟨B, D, ⟨U⟩, ⟨S⟩⟩ := h
  have hx : x ∈ ⋃ i, U.region i := U.cover.symm ▸ mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  fin_cases i
  · obtain ⟨a, _, rfl⟩ := (U.identify 0).map_image.symm.subset hi
    obtain ⟨y, ⟨E⟩⟩ := S.first_factor a
    exact ⟨y, ⟨E.trans (RepairedGroupFactorData.ofMulEquiv (U.inclusionGroupEquiv 0 a))⟩⟩
  · obtain ⟨a, _, rfl⟩ := (U.identify 1).map_image.symm.subset hi
    obtain ⟨y, ⟨E⟩⟩ := S.second_factor a
    exact ⟨y, ⟨E.trans (RepairedGroupFactorData.ofMulEquiv (U.inclusionGroupEquiv 1 a))⟩⟩



theorem factors_of_reflTransGen {A C : GeneralizedSliceCarrier.{u}}
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) (x : A.carrier) :
    ∃ y : C.carrier,
      Nonempty (RepairedGroupFactorData (FundamentalGroup C.carrier y)
        (FundamentalGroup A.carrier x)) := by
  induction h with
  | refl => exact ⟨x, ⟨RepairedGroupFactorData.ofMulEquiv (MulEquiv.refl _)⟩⟩
  | tail _ hnext ih =>
    obtain ⟨b, ⟨E⟩⟩ := ih
    obtain ⟨c, ⟨D⟩⟩ := hnext.factor b
    exact ⟨c, ⟨D.trans E⟩⟩

end SmoothConnectedSumStep

namespace SmoothFiniteConnectedSumAssembly




theorem piece_factor {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}} (R : SmoothFiniteConnectedSumAssembly pieces C)
    (i : Fin n) (x : (pieces i).carrier) :
    ∃ y : C.carrier,
      Nonempty (RepairedGroupFactorData (FundamentalGroup C.carrier y)
        (FundamentalGroup (pieces i).carrier x)) := by
  obtain ⟨y, ⟨D⟩⟩ := SmoothConnectedSumStep.factors_of_reflTransGen R.operations
    ((R.disjoint_union.identify i).map x)
  exact ⟨y, ⟨D.trans (RepairedGroupFactorData.ofMulEquiv
    (R.disjoint_union.inclusionGroupEquiv i x).symm)⟩⟩

end SmoothFiniteConnectedSumAssembly



theorem repairedSurgeryGroupEffects {A B : GeneralizedSliceCarrier.{u}}
    (C : SurgeryTopologyConclusion A B) : Nonempty (RepairedSurgeryGroupEffectsData C) := by
  classical
  choose b hb using C.reconstruction.piece_factor
  exact ⟨{
    parent_basepoint := fun i _ x => b i x
    piece_effect := fun i _ x => Classical.choice (hb i x) }⟩

end PoincareConjecture
