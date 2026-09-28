import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.ConnectedRemainder
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.ClosedCoverLabels

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem isConnected_card_two_cap_boundary_remainder
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] (hcard : Nat.card ι = 2)
    {B S U : Set E} (hB : IsFinitePLBallPair (Fin 3 → ℝ) B S)
    (A a : ι → Set E) (hA : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (A i) (a i))
    (hdis : Pairwise fun i j => Disjoint (A i) (A j)) (hU : IsClosed U)
    (hcontact : ∀ i, U ∩ A i = a i) (hcover : U ∪ (⋃ i, A i) = S) :
    IsConnected U := by
  classical
  let := Fintype.ofFinite ι
  let e : Bool ≃ ι := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_bool,Nat.card_eq_fintype_card] using hcard.symm)
  have hcover' : (U ∪ A (e false)) ∪ A (e true) = S := by
    rw [←hcover,union_assoc]
    congr 1
    ext x
    constructor
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨e false,hx⟩
      · exact mem_iUnion.mpr ⟨e true,hx⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      obtain ⟨b,rfl⟩ := e.surjective i
      cases b
      · exact Or.inl hi
      · exact Or.inr hi
  exact isConnected_two_cap_boundary_remainder hB (A ∘ e) (a ∘ e) (fun b => hA (e b))
    (hdis (e.injective.ne (by decide))) hU (fun b => hcontact (e b)) hcover'

end PoincareConjecture.M76.PrismBelt
