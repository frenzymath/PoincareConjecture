import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Factors

/-! Adapted from Mapher `PoincareMT/Proofs/M54/ConnectedSum/Reconstruction.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Finite reconstruction and survivor group certificates

The initial clopen disjoint union gives a group isomorphism for each
summand. Every connected-sum operation supplies a retraction at each
old basepoint. Composition along the finite reconstruction proves the
group effects of Morgan--Tian Proposition 15.3 (pp. 357-358).
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT

namespace SmoothDisjointUnionData

/-- A summand and its clopen image have the same based fundamental group
in the initial disjoint union (MT Proposition 15.3, pp. 357-358). -/
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

/-- One reconstruction operation preserves each old based group as a
retract of an appropriate new based group (MT Proposition 15.3, pp. 357-358). -/
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

/-- Compose the based factor certificates through a finite sequence of
actual connected sums (MT Proposition 15.3, pp. 357-358). -/
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

/-- Every original summand group is a retract of a group of the finite
reconstruction, including disconnected or empty intermediate carriers.
Source: MT Proposition 15.3, pp. 357-358. -/
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

/-- Assemble the van Kampen factor maps, named kernels and injective
sections for the surviving summands of MT Proposition 15.3, pp. 357-358. -/
theorem repairedSurgeryGroupEffects {A B : GeneralizedSliceCarrier.{u}}
    (C : SurgeryTopologyConclusion A B) : Nonempty (RepairedSurgeryGroupEffectsData C) := by
  classical
  choose b hb using C.reconstruction.piece_factor
  exact ⟨{
    parent_basepoint := fun i _ x => b i x
    piece_effect := fun i _ x => Classical.choice (hb i x) }⟩

end PoincareMT
