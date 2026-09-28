import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentEmbedding

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_marked_image_homeomorph
    {ι κ α E : Type*} [Fintype ι] [Fintype κ]
    [TopologicalSpace E] [T2Space E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι)
    (F : LatticeHandleAmbient ι κ L → E) (hF : Continuous F)
    (hinj : InjOn F (latticeHandleDomain ι κ L))
    (C : Set ((ι → ℝ) × (κ → ℝ))) (hC : IsCompact C)
    (hCpatch : C ⊆ sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2))
    (T : Set E) (hT : T = F '' (hamiltonMarkedProjection ι κ L '' C)) :
    ∃ H : C ≃ₜ T,
      ∀ x, (H x : E) = F (hamiltonMarkedProjection ι κ L x) := by
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hzero, _⟩ | ⟨_, _, _, _, _, hmark⟩
    · omega
    · exact hmark
  have hm (x) (hx : x ∈ C) :
      hamiltonMarkedProjection ι κ L x ∈ latticeHandleDomain ι κ L :=
    b.subset_domain (hmark.symm.subset ⟨x, hCpatch hx, rfl⟩).1
  let f : C → T := fun x =>
    ⟨F (hamiltonMarkedProjection ι κ L x), hT.symm.subset ⟨_, ⟨x, x.property, rfl⟩, rfl⟩⟩
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact hF.comp ((continuous_fst.prodMk
      (QuotientAddGroup.continuous_mk.comp continuous_snd)).comp continuous_subtype_val)
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact b.markedProjection_injOn_attaching_patch hpos (hCpatch x.property)
      (hCpatch y.property) (hinj (hm x x.property) (hm y y.property)
        (congrArg Subtype.val hxy))
  have hfs : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hT.subset hz
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨(hf.isClosedEmbedding hfi).isEmbedding.toHomeomorphOfSurjective hfs, fun _ => rfl⟩

end PoincareConjecture.M76
