import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.SourceCopies



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)



theorem square_pair_cross_fiber_of_tube_preimage
    {X : Type*} {d q : P2 → X} {U : Set X}
    (hpre : ∀ z : Sq, d z ∈ U ↔ (z : P2).1 = 0 ∨ (z : P2).1 = 1)
    (hqU : MapsTo q Sq U) (hqi : InjOn q Sq)
    (hleft : ∀ t : I, d (0, t) = q (0, t))
    (hright : ∀ t : I, d (1, t) = q (1, t)) (u v : Sq) :
    d u = q v ↔ u = v ∧ ((u : P2).1 = 0 ∨ (u : P2).1 = 1) := by
  have hagree (z : Sq) (hz : (z : P2).1 = 0 ∨ (z : P2).1 = 1) : d z = q z := by
    rcases hz with hz | hz
    · rw [show (z : P2) = (0, z.val.2) from Prod.ext hz rfl]
      exact hleft ⟨z.val.2, z.property.2⟩
    · rw [show (z : P2) = (1, z.val.2) from Prod.ext hz rfl]
      exact hright ⟨z.val.2, z.property.2⟩
  constructor
  · intro huv
    have hside := (hpre u).mp (huv ▸ hqU v.property)
    exact ⟨Subtype.ext (hqi u.property v.property ((hagree u hside).symm.trans huv)), hside⟩
  · rintro ⟨rfl, hside⟩
    exact hagree u hside

namespace AnnulusSquareCopies



theorem double_points_eq_retained
    {X : Type*} {f : Fin 2 → P2 → X} {g : P2 → X}
    (C : AnnulusSquareCopies f g) {U : Set X}
    (hpre : ∀ z : Sq, f 0 z ∈ U ↔ (z : P2).1 = 0 ∨ (z : P2).1 = 1)
    (hqU : MapsTo (f 1) Sq U) (hqi : InjOn (f 1) Sq)
    (hleft : ∀ t : I, f 0 (0, t) = f 1 (0, t))
    (hright : ∀ t : I, f 0 (1, t) = f 1 (1, t)) :
    {x : P2 | x ∈ squareAnnulus 8 1 ∧
      ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g y = g x} =
    (fun z : Sq ↦ (C.chart 0 z : P2)) ''
      {u : Sq | ∃ v : Sq, v ≠ u ∧ f 0 v = f 0 u} := by
  have hcross := square_pair_cross_fiber_of_tube_preimage hpre hqU hqi hleft hright
  ext x
  constructor
  · rintro ⟨hx, y, hy, hyx, hval⟩
    obtain ⟨j, u, rfl⟩ := C.exists_representation hx
    obtain ⟨k, v, rfl⟩ := C.exists_representation hy
    rw [C.val, C.val] at hval
    fin_cases j <;> fin_cases k
    · refine ⟨u, ⟨v, ?_, hval⟩, rfl⟩
      intro he
      exact hyx (congrArg (fun z : Sq ↦ (C.chart 0 z : P2)) he)
    · exact (hyx ((C.cross u v).mpr ((hcross u v).mp hval.symm)).symm).elim
    · exact (hyx ((C.cross v u).mpr ((hcross v u).mp hval))).elim
    · have he := hqi v.property u.property hval
      exact (hyx (congrArg (fun z : Sq ↦ (C.chart 1 z : P2)) (Subtype.ext he))).elim
  · rintro ⟨u, ⟨v, hv, hval⟩, rfl⟩
    refine ⟨C.chart_mem 0 u, C.chart 0 v, C.chart_mem 0 v, ?_, ?_⟩
    · intro he
      exact hv ((C.chart 0).injective (Subtype.ext he))
    · simpa only [C.val] using hval

end AnnulusSquareCopies

end PoincareConjecture.M76.Dehn
