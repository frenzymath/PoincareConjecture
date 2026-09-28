import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_original_open_neighborhood_of_carrier_neighborhood
    {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [TopologicalSpace Y]
    (K : SimplicialComplex ℝ E) {C : Set X} (H : C ≃ₜ K.space)
    (g : E → C) (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {S : Set E} (hSK : S ⊆ K.space) (x : K.space)
    {V : Set K.space} (hV : IsOpen V) (hxV : x ∈ V)
    (hVS : Subtype.val '' V ⊆ S) (hxC : (g x : X) ∈ interior C)
    (B : OpenPartialHomeomorph X Y)
    (hsource : MapsTo (fun z => (g z : X)) S B.source) :
    InjOn (fun z => B (g z)) S ∧
      (∃ O : Set X, IsOpen O ∧ (g x : X) ∈ O ∧
        O ⊆ interior C ∩ B.source ∧
        O ⊆ (fun z => (g z : X)) '' S) ∧
      B (g x) ∈ interior ((fun z => B (g z)) '' S) := by
  have hxS : (x : E) ∈ S := hVS ⟨x, hxV, rfl⟩
  have hHgx : H (g x) = x := by
    have h : g x = H.symm x := Subtype.ext (hg x)
    rw [h, H.apply_symm_apply]
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp (hV.preimage H.continuous)
  have hxU : (g x : X) ∈ U := by
    have h : g x ∈ H ⁻¹' V := by
      change H (g x) ∈ V
      rw [hHgx]
      exact hxV
    rw [← hUV] at h
    exact h
  let O := U ∩ (interior C ∩ B.source)
  have hO : IsOpen O := hU.inter (isOpen_interior.inter B.open_source)
  have hxO : (g x : X) ∈ O := ⟨hxU, hxC, hsource hxS⟩
  have hOS : O ⊆ (fun z => (g z : X)) '' S := by
    intro y hy
    let yC : C := ⟨y, interior_subset hy.2.1⟩
    have hyV : H yC ∈ V := by
      change yC ∈ H ⁻¹' V
      rw [← hUV]
      exact hy.1
    refine ⟨H yC, hVS ⟨H yC, hyV, rfl⟩, ?_⟩
    exact (hg (H yC)).trans (congrArg Subtype.val (H.symm_apply_apply yC))
  refine ⟨?_, ⟨O, hO, hxO, fun _ hy => hy.2, hOS⟩, ?_⟩
  · intro z hz w hw hzw
    have hgw : (g z : X) = (g w : X) := B.injOn (hsource hz) (hsource hw) hzw
    have hinv : H.symm ⟨z, hSK hz⟩ = H.symm ⟨w, hSK hw⟩ :=
      Subtype.ext ((hg ⟨z, hSK hz⟩).symm.trans (hgw.trans (hg ⟨w, hSK hw⟩)))
    exact congrArg Subtype.val (H.symm.injective hinv)
  · have himage : B '' O ⊆ (fun z => B (g z)) '' S := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := hOS hy
      exact ⟨z, hz, congrArg B hzy⟩
    exact interior_maximal himage
      (B.isOpen_image_of_subset_source hO (fun _ hy => hy.2.2))
      (mem_image_of_mem B hxO)

end Geometry.SimplicialComplex
