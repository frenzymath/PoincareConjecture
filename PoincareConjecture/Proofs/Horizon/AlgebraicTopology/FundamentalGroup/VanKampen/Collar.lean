import PoincareConjecture.Proofs.M54.Mathlib.VanKampenGeneral
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace VanKampen

variable {X G : Type*} [TopologicalSpace X] [Group G]

theorem exists_hom_mem_range_of_union
    (U C : Set X) (hU : IsOpen U) (hC : IsOpen C)
    (hpath : IsPathConnected C) (hoverlap : IsSimplyConnected (U ∩ C))
    (k : G) (hfactor : ∀ b : U, ∃ f : FundamentalGroup U b →* G, k ∈ f.range)
    (b : (U ∪ C : Set X)) (hb : b.1 ∈ C) :
    ∃ f : FundamentalGroup (U ∪ C : Set X) b →* G, k ∈ f.range := by
  let W : Set X := U ∪ C
  let U' : Set W := Subtype.val ⁻¹' U
  let C' : Set W := Subtype.val ⁻¹' C
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  have hC' : IsOpen C' := hC.preimage continuous_subtype_val
  have hcover : U' ∪ C' = univ := by
    ext x
    exact iff_true_intro x.property
  have hinter : IsSimplyConnected (U' ∩ C') := by
    have he : (Subtype.val : W → X) '' (U' ∩ C') = U ∩ C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, Or.inl hx.1⟩, hx, rfl⟩
    exact (Topology.IsEmbedding.subtypeVal.isSimplyConnected_image).mp (he ▸ hoverlap)
  obtain ⟨x, hxU, hxC⟩ := hoverlap.nonempty
  let a : W := ⟨x, Or.inl hxU⟩
  let a' : U' := ⟨a, hxU⟩
  let e : U' ≃ₜ U := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (show U ⊆ range (Subtype.val : W → X) from fun y hy => ⟨⟨y, Or.inl hy⟩, rfl⟩)
  obtain ⟨f, z, hz⟩ := hfactor (e a')
  let E := e.fundamentalGroupMulEquiv a'
  obtain ⟨r, hr⟩ := exists_retraction U' C' a' hU' hC' hcover hinter
  have hpath' : Joined a b :=
    ((hpath.preimage_coe subset_union_right).joinedIn a hxC b hb).joined
  let B := FundamentalGroup.fundamentalGroupMulEquivOfPath hpath'.somePath
  refine ⟨(f.comp E.toMonoidHom).comp (r.comp B.symm.toMonoidHom),
    B (FundamentalGroup.map (inclusion U') a' (E.symm z)), ?_⟩
  change f (E (r (B.symm (B (FundamentalGroup.map (inclusion U') a' (E.symm z)))))) = k
  have hr' : r (FundamentalGroup.map (inclusion U') a' (E.symm z)) = E.symm z :=
    DFunLike.congr_fun hr (E.symm z)
  rw [B.symm_apply_apply, hr', E.apply_symm_apply]
  exact hz

end VanKampen
