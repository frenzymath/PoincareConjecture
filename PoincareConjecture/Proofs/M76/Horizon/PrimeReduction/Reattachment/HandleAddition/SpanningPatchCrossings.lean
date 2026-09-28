import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalSpherePatchReplacement

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.patch_pair_charts_off_ball
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q T S F A r : Set X}
    (u : ChartwisePLBall e Q T) (hAT : A ⊆ T)
    (hcross : ∀ x ∈ S ∩ F,
      ∃ H : OpenPartialHomeomorph X V3,
        x ∈ H.source ∧ H x = 0 ∧
        (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
        ∀ y ∈ H.source,y ∈ F ↔ H y 0 = 0) :
    ∀ x ∈ ((S \ (A \ r)) ∪ (T \ (A \ r))) ∩ F, x ∉ Q →
      ∃ H : OpenPartialHomeomorph X V3,
        x ∈ H.source ∧ H x = 0 ∧ H.source ⊆ Qᶜ ∧
        (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source,y ∈ (S \ (A \ r)) ∪ (T \ (A \ r)) ↔ H y 1 = 0) ∧
        ∀ y ∈ H.source,y ∈ F ↔ H y 0 = 0 := by
  have hlocal (y : X) (hy : y ∉ Q) :
      y ∈ (S \ (A \ r)) ∪ (T \ (A \ r)) ↔ y ∈ S := by
    constructor
    · rintro (h | h)
      · exact h.1
      · exact (hy (u.boundary_subset h.1)).elim
    · exact fun h => Or.inl ⟨h,fun hn => hy (u.boundary_subset (hAT hn.1))⟩
  intro x hx hxQ
  obtain ⟨H,hxH,hHx,hHe,hHS,hHF⟩ := hcross x ⟨(hlocal x hxQ).mp hx.1,hx.2⟩
  let P := H.restrOpen Qᶜ u.isCompact.isClosed.isOpen_compl
  refine ⟨P,⟨hxH,hxQ⟩,hHx,fun y hy => hy.2,?_,?_,?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right H (hHe i) u.isCompact.isClosed.isOpen_compl
  · intro y hy
    exact (hlocal y hy.2).trans (hHS y hy.1)
  · intro y hy
    exact hHF y hy.1

end PoincareConjecture.M76
