import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusBoundaryInventory
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualLabelOrder

set_option autoImplicit false

open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical

noncomputable def residualBoundarySide
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : AbstractSimplicialComplex V}
    {P : SimpleGraph V}
    {L : Finset (Edge A.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) (b : Bool) :
    OriginalTorusBoundarySide (A := A) P L :=
  (Sum.inr ((Finset.equivFinOfCardEq hL).symm i), b)

theorem residualBoundarySide_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : AbstractSimplicialComplex V}
    {P : SimpleGraph V}
    {L : Finset (Edge A.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) :
    Function.Injective (fun x : Fin 2 × Bool => residualBoundarySide (P := P) hL x.1 x.2) := by
  intro x y h
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  apply Prod.ext
  · have hfirst := congrArg Prod.fst h
    simp only [residualBoundarySide] at hfirst
    exact (Finset.equivFinOfCardEq hL).symm.injective (Sum.inr.inj hfirst)
  · have hsecond := congrArg Prod.snd h
    simpa only [residualBoundarySide] using hsecond

theorem residualBoundarySide_opposite
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : AbstractSimplicialComplex V}
    {P : SimpleGraph V}
    {L : Finset (Edge A.toPreAbstractSimplicialComplex)}
    (I : OriginalTorusBoundarySideInventory (A := A) P L)
    (hL : L.card = 2) (i : Fin 2) (b : Bool) :
    I.opposite (residualBoundarySide hL i b) =
      residualBoundarySide hL i (!b) := by
  apply Prod.ext
  · exact I.opposite_first _
  · exact I.opposite_second _

theorem residualBoundarySide_surjective
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : AbstractSimplicialComplex V}
    {P : SimpleGraph V}
    {L : Finset (Edge A.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) {s : OriginalTorusBoundarySide (A := A) P L}
    (hs : ∃ r : {e : Edge A.toPreAbstractSimplicialComplex // e ∈ L},
      s.1 = Sum.inr r) :
    ∃ i : Fin 2, ∃ b : Bool, residualBoundarySide hL i b = s := by
  rcases s with ⟨label, b⟩
  rcases hs with ⟨r, hr⟩
  rcases label with p | r'
  · simp at hr
  · have hr' : r' = r := by simpa using hr
    subst r'
    obtain ⟨i, hi⟩ := (Finset.equivFinOfCardEq hL).symm.surjective r
    refine ⟨i, b, ?_⟩
    simp only [residualBoundarySide]
    rw [hi]

end PoincareConjecture.M76
