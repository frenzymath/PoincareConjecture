import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreComponentCount

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem cocore_section_partition_of_contact_deletion
    {X : Type*} [TopologicalSpace X]
    (Q : OpenPartialHomeomorph X V3) {J L : Set V3}
    (hJQ : J ⊆ Q.target) (hLQ : L ⊆ Q.target)
    (A : V3 → ℝ) (t : ℝ) {S : Set X} (N : Bool → Set X)
    (hcontact : (N true ∪ N false) ∩ Q.symm '' (Q.target ∩ {x | A x = t}) =
      (S ∩ Q.symm '' (Q.target ∩ {x | A x = t})) \ Q.symm '' L) :
    ((Q '' (N true ∩ Q.source) ∩ J) ∩ {x | A x = t}) ∪
        ((Q '' (N false ∩ Q.source) ∩ J) ∩ {x | A x = t}) =
      ((Q '' (S ∩ Q.source) ∩ J) ∩ {x | A x = t}) \ L := by
  have hmem (T : Set X) {x : V3} (hx : x ∈ Q.target) :
      x ∈ Q '' (T ∩ Q.source) ↔ Q.symm x ∈ T := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [Q.left_inv hy.2] using hy.1
    · intro h
      exact ⟨Q.symm x,⟨h,Q.map_target hx⟩,Q.right_inv hx⟩
  ext x
  constructor
  · intro hx
    have hxJ : x ∈ J := hx.elim (fun h => h.1.2) (fun h => h.1.2)
    have hxT : A x = t := hx.elim (fun h => h.2) (fun h => h.2)
    have hxQ := hJQ hxJ
    have hnew : Q.symm x ∈ N true ∪ N false :=
      hx.elim (fun h => Or.inl ((hmem _ hxQ).mp h.1.1))
        (fun h => Or.inr ((hmem _ hxQ).mp h.1.1))
    have hphys := hcontact.subset ⟨hnew,⟨x,⟨hxQ,hxT⟩,rfl⟩⟩
    exact ⟨⟨⟨(hmem _ hxQ).mpr hphys.1.1,hxJ⟩,hxT⟩,
      fun h => hphys.2 (mem_image_of_mem Q.symm h)⟩
  · rintro ⟨hx,hxL⟩
    have hxQ := hJQ hx.1.2
    have hn : Q.symm x ∉ Q.symm '' L := by
      rintro ⟨y,hy,hyx⟩
      exact hxL ((Q.symm.injOn (hLQ hy) hxQ hyx) ▸ hy)
    have hphys := hcontact.superset
      ⟨⟨(hmem _ hxQ).mp hx.1.1,⟨x,⟨hxQ,hx.2⟩,rfl⟩⟩,hn⟩
    exact hphys.1.elim
      (fun h => Or.inl ⟨⟨(hmem _ hxQ).mpr h,hx.1.2⟩,hx.2⟩)
      (fun h => Or.inr ⟨⟨(hmem _ hxQ).mpr h,hx.1.2⟩,hx.2⟩)

end PoincareConjecture.M76
