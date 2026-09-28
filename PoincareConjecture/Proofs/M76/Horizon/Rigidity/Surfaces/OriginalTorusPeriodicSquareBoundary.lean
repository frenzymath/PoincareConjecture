import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PeriodicSquare
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualSideOrder











set_option autoImplicit false

open Set Topology PreAbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.PeriodicSquare

variable (p : ℝ) [Fact (0 < p)]

private def zeroPoint : Icc (0 : ℝ) p := ⟨0, le_rfl, le_of_lt (Fact.out : (0 : ℝ) < p)⟩

private def periodPoint : Icc (0 : ℝ) p := ⟨p, le_of_lt (Fact.out : (0 : ℝ) < p), le_rfl⟩


def sidePoint (i : Fin 2) (b : Bool) (t : Icc (0 : ℝ) p) : Square p :=
  if i = 0 then
    if b then (t, periodPoint p) else (t, zeroPoint p)
  else
    if b then (periodPoint p, t) else (zeroPoint p, t)

theorem continuous_sidePoint (i : Fin 2) (b : Bool) :
    Continuous (sidePoint p i b) := by
  by_cases hi : i = 0
  · subst i
    cases b
    · change Continuous (fun t : Icc (0 : ℝ) p => (t, zeroPoint p))
      exact continuous_id.prodMk continuous_const
    · change Continuous (fun t : Icc (0 : ℝ) p => (t, periodPoint p))
      exact continuous_id.prodMk continuous_const
  · have hi' : i = 1 := by
      apply Fin.eq_of_val_eq
      omega
    subst i
    cases b
    · change Continuous (fun t : Icc (0 : ℝ) p => (zeroPoint p, t))
      exact continuous_const.prodMk continuous_id
    · change Continuous (fun t : Icc (0 : ℝ) p => (periodPoint p, t))
      exact continuous_const.prodMk continuous_id


def sideFlip (x : Fin 2 × Bool) : Fin 2 × Bool := (x.1, !x.2)

def sidePairRelation (x y : Fin 2 × Bool) : Prop := y = sideFlip x

theorem sideFlip_involutive : Function.Involutive sideFlip := by
  intro x
  rcases x with ⟨i, b⟩
  cases b <;> rfl

theorem sidePairRelation_eqvgen_iff {x y : Fin 2 × Bool} :
    Relation.EqvGen sidePairRelation x y ↔ x.1 = y.1 := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact (congrArg Prod.fst h).symm
    | refl x => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  · intro h
    rcases x with ⟨i, b⟩
    rcases y with ⟨j, c⟩
    simp only [Prod.fst] at h
    subst j
    cases b with
    | false =>
        cases c with
        | false => exact Relation.EqvGen.refl _
        | true => exact Relation.EqvGen.rel _ _ rfl
    | true =>
        cases c with
        | false =>
            exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ rfl)
        | true => exact Relation.EqvGen.refl _

theorem sidePoint_sidePair (i : Fin 2) (t : Icc (0 : ℝ) p) :
    SidePair p (sidePoint p i false t) (sidePoint p i true t) := by
  by_cases hi : i = 0
  · subst i
    simp [sidePoint, SidePair, zeroPoint, periodPoint]
  · have hi' : i = 1 := by
      apply Fin.eq_of_val_eq
      omega
    subst i
    simp [sidePoint, SidePair, zeroPoint, periodPoint]

theorem sidePoint_projection_eq_opposite (i : Fin 2) (b : Bool)
    (t : Icc (0 : ℝ) p) :
    projection p (sidePoint p i b t) =
      projection p (sidePoint p i (!b) t) := by
  cases b
  · exact projection_eq_of_sidePair p (sidePoint_sidePair p i t)
  · exact (projection_eq_of_sidePair p (sidePoint_sidePair p i t)).symm

theorem sidePoint_projection_eq_opposite_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : AbstractSimplicialComplex V}
    {P : SimpleGraph V}
    {L : Finset (Edge A.toPreAbstractSimplicialComplex)}
    (I : OriginalTorusBoundarySideInventory (A := A) P L)
    (hL : L.card = 2) (i : Fin 2) (b : Bool)
    (t : Icc (0 : ℝ) p) :
    projection p (sidePoint p i b t) =
      projection p (sidePoint p i (!b) t) ∧
      I.opposite (residualBoundarySide hL i b) =
        residualBoundarySide hL i (!b) := by
  exact ⟨sidePoint_projection_eq_opposite p i b t,
    residualBoundarySide_opposite I hL i b⟩

end PoincareConjecture.M76.PeriodicSquare
