import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentEmbedding








set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_attaching_disk_parametrization
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    ∃ H : closedBall (0 : κ → ℝ) (3/2) ≃ₜ
        ((QuotientAddGroup.mk : (κ→ℝ) → (κ→ℝ) ⧸ L.toAddSubgroup) ''
          closedBall (0 : κ→ℝ) (3/2)),
      (∀ x, (H x : (κ→ℝ) ⧸ L.toAddSubgroup) = QuotientAddGroup.mk x.val) ∧
      (∀ x, (QuotientAddGroup.mk (H.symm x).val : (κ→ℝ) ⧸ L.toAddSubgroup) = x.val) ∧
      ∀ x, (H x : (κ→ℝ) ⧸ L.toAddSubgroup) ∈
        (QuotientAddGroup.mk : (κ→ℝ) → (κ→ℝ) ⧸ L.toAddSubgroup) ''
          sphere (0 : κ→ℝ) (3/2) ↔ x.val ∈ sphere (0 : κ→ℝ) (3/2) := by
  let C := closedBall (0 : κ→ℝ) (3/2)
  let q : (κ→ℝ) → (κ→ℝ) ⧸ L.toAddSubgroup := QuotientAddGroup.mk
  let f : C → q '' C := fun x => ⟨q x,⟨x,x.property,rfl⟩⟩
  have : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hc : Continuous f :=
    (QuotientAddGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := by
    intro x y hh
    exact Subtype.ext (b.quotient_injOn_attaching_disk hpos x.property y.property
      (congrArg Subtype.val hh))
  have hs : Function.Surjective f := by
    rintro ⟨x,y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩
  let H := (hc.isClosedEmbedding hi).isEmbedding.toHomeomorphOfSurjective hs
  refine ⟨H,fun _ => rfl,?_,?_⟩
  · intro x
    exact congrArg Subtype.val (H.apply_symm_apply x)
  · intro x
    constructor
    · rintro ⟨y,hy,hyx⟩
      have hyx' := b.quotient_injOn_attaching_disk hpos (sphere_subset_closedBall hy)
        x.property hyx
      exact hyx' ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩

theorem HamiltonMarkedProtectedBall.contractible_attaching_disk
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    ContractibleSpace ((QuotientAddGroup.mk : (κ→ℝ) → (κ→ℝ) ⧸ L.toAddSubgroup) ''
      closedBall (0 : κ→ℝ) (3/2)) := by
  obtain ⟨H,_,_,_⟩ := b.exists_attaching_disk_parametrization hpos
  let : ContractibleSpace (closedBall (0 : κ→ℝ) (3/2)) :=
    (convex_closedBall (0 : κ→ℝ) (3/2)).contractibleSpace
      ⟨0,mem_closedBall_self (by norm_num)⟩
  exact H.symm.contractibleSpace

end PoincareConjecture.M76
