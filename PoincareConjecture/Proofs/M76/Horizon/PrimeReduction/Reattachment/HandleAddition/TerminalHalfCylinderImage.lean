import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcCoordinates

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

theorem closed_half_cylinder_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {T B : Set X} (W : (Y × J) ≃ₜ T) (H : (Y × I) ≃ₜ B) (side : Bool)
    (hcoords : ∀ z, ∃ w, w.1 = z.1 ∧
      (w.2 : ℝ) = (if side then 1 - (z.2 : ℝ) else (z.2 : ℝ) - 1) ∧
      (H z : X) = W w) :
    B = (fun z => (W z : X)) ''
      {z : Y × J | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0} := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨z,hz⟩ := H.surjective ⟨x,hx⟩
    obtain ⟨w,_,hw,hval⟩ := hcoords z
    refine ⟨w,?_,hval.symm.trans (congrArg Subtype.val hz)⟩
    change (if side then 0 ≤ (w.2 : ℝ) else (w.2 : ℝ) ≤ 0)
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hw ⊢ <;>
      linarith [z.2.property.1,z.2.property.2]
  · rintro x ⟨w,hw,rfl⟩
    let t : I := ⟨if side then 1 - (w.2 : ℝ) else (w.2 : ℝ) + 1,by
      change (if side then 0 ≤ (w.2 : ℝ) else (w.2 : ℝ) ≤ 0) at hw
      cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hw ⊢ <;>
        constructor <;> linarith [w.2.property.1,w.2.property.2]⟩
    obtain ⟨v,hv1,hv2,hval⟩ := hcoords (w.1,t)
    have hvw : v = w := by
      apply Prod.ext hv1
      apply Subtype.ext
      cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,t] at hv2 <;>
        linarith
    rw [hvw] at hval
    change (W w : X) ∈ B
    rw [←hval]
    exact (H (w.1,t)).property

theorem closed_half_cylinder_old_endpoint
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {T B : Set X} (W : (Y × J) ≃ₜ T) (H : (Y × I) ≃ₜ B) (side : Bool)
    (hcoords : ∀ z, ∃ w, w.1 = z.1 ∧
      (w.2 : ℝ) = (if side then 1 - (z.2 : ℝ) else (z.2 : ℝ) - 1) ∧
      (H z : X) = W w) (y : Y) :
    (H (y,0) : X) = W (y,⟨if side then 1 else -1,by cases side <;> norm_num⟩) := by
  obtain ⟨w,hw1,hw2,hval⟩ := hcoords (y,0)
  have hw : w = (y,⟨if side then 1 else -1,by cases side <;> norm_num⟩) := by
    apply Prod.ext hw1
    apply Subtype.ext
    cases side <;> simpa using hw2
  exact hval.trans (congrArg (fun z => (W z : X)) hw)

end PoincareConjecture.M76
