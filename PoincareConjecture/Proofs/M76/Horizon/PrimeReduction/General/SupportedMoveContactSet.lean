import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalComplexEdgeGeometry










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76





theorem inter_image_symm_eq_inter_diff
    {X : Type*} [TopologicalSpace X] (G : X ≃ₜ X)
    {e S w W : Set X}
    (hedge : G '' e = (e \ w) ∪ W)
    (hfix : EqOn G id (e \ w))
    (hdisj : Disjoint W S) :
    e ∩ (G.symm '' S) = (e \ w) ∩ S := by
  ext x
  constructor
  · rintro ⟨hxe, y, hys, hyx⟩
    have hGx : G x = y := by
      apply G.injective
      simpa using (congrArg G hyx).symm
    have hsplit : G x ∈ (e \ w) ∪ W := by
      rw [← hedge]
      exact ⟨x, hxe, rfl⟩
    rcases hsplit with hret | hrep
    · have hGfix : G (G x) = G x := hfix hret
      have hxx : G x = x := G.injective hGfix
      have hxy : y = x := hGx.symm.trans hxx
      exact ⟨hxx ▸ hret, hxy ▸ hys⟩
    · exact (disjoint_left.mp hdisj (hGx ▸ hrep) hys).elim
  · rintro ⟨hret, hys⟩
    refine ⟨hret.1, x, hys, ?_⟩
    apply G.injective
    simpa [hfix hret]



theorem inter_image_symm_eq_of_fixed
    {X : Type*} [TopologicalSpace X] (G : X ≃ₜ X)
    {A S : Set X}
    (hfix : EqOn G id A) :
    A ∩ (G.symm '' S) = A ∩ S := by
  ext x
  constructor
  · rintro ⟨hxa, y, hys, hyx⟩
    have hGx : G x = y := by
      apply G.injective
      simpa using (congrArg G hyx).symm
    have hxx : G x = x := hfix hxa
    have hxy : y = x := hGx.symm.trans hxx
    exact ⟨hxa, hxy ▸ hys⟩
  · rintro ⟨hxa, hxs⟩
    refine ⟨hxa, x, hxs, ?_⟩
    apply G.injective
    simpa [hfix hxa]


theorem ncard_inter_image_symm_eq_of_fixed
    {X : Type*} [TopologicalSpace X] (G : X ≃ₜ X)
    {A S : Set X}
    (hfix : EqOn G id A) :
    (A ∩ (G.symm '' S)).ncard = (A ∩ S).ncard := by
  rw [inter_image_symm_eq_of_fixed G hfix]



theorem ncard_untouched_edge_contacts_after_supported_move
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (G : X ≃ₜ X) {edges : ι → Set X} {S : Set X}
    (hfixed : ∀ i, EqOn G id (edges i)) :
    ∀ i, (edges i ∩ (G.symm '' S)).ncard = (edges i ∩ S).ncard := by
  intro i
  exact ncard_inter_image_symm_eq_of_fixed G (hfixed i)




theorem ncard_inter_image_symm_eq_sub_two
    {X : Type*} [TopologicalSpace X] (G : X ≃ₜ X)
    {e S w W : Set X} {u v : X}
    (hedge : G '' e = (e \ w) ∪ W)
    (hfix : EqOn G id (e \ w))
    (hdisj : Disjoint W S)
    (hcontact : (e \ w) ∩ S = (e ∩ S) \ ({u, v} : Set X))
    (hfin : (e ∩ S).Finite)
    (hu : u ∈ e ∩ S) (hv : v ∈ e ∩ S) ( huv : u ≠ v) :
    (e ∩ (G.symm '' S)).ncard = (e ∩ S).ncard - 2 := by
  rw [inter_image_symm_eq_inter_diff G hedge hfix hdisj, hcontact]
  have hpair : ({u, v} : Set X) ⊆ e ∩ S := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  rw [Set.ncard_sdiff' hpair hfin]
  simp [huv]

end PoincareConjecture.M76
