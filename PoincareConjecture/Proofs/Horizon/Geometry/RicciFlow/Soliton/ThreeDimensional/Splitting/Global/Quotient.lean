import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Orientation

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}

def nullOrientationOrbitSetoid (C : NullOrientationCover D) :
    Setoid (UnitRicciKernel D) where
  r p q := q = p ∨ q = C.deck p
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact Or.inl rfl
    · intro p q hpq
      rcases hpq with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by rw [h, C.deck_involutive])
    · intro p q r hpq hqr
      rcases hpq with hpq | hpq <;> rcases hqr with hqr | hqr
      · exact Or.inl (hqr.trans hpq)
      · exact Or.inr (hqr.trans (congrArg C.deck hpq))
      · exact Or.inr (hqr.trans hpq)
      · exact Or.inl (hqr.trans (by rw [hpq, C.deck_involutive]))

abbrev NullOrientationQuotient (C : NullOrientationCover D) :=
  Quotient (nullOrientationOrbitSetoid C)

def nullOrientationQuotientMap (C : NullOrientationCover D) :
    UnitRicciKernel D → NullOrientationQuotient C :=
  Quotient.mk (nullOrientationOrbitSetoid C)

omit [T2Space M] [ConnectedSpace M] in
theorem nullOrientationQuotientMap_surjective (C : NullOrientationCover D) :
    Function.Surjective (nullOrientationQuotientMap C) :=
  Quotient.mk_surjective

omit [T2Space M] [ConnectedSpace M] in
theorem nullOrientationQuotientMap_eq_iff (C : NullOrientationCover D)
    (p q : UnitRicciKernel D) :
    nullOrientationQuotientMap C p = nullOrientationQuotientMap C q ↔
    q = p ∨ q = C.deck p := by
  change Quotient.mk (nullOrientationOrbitSetoid C) p =
    Quotient.mk (nullOrientationOrbitSetoid C) q ↔ _
  exact Quotient.eq'

omit [T2Space M] [ConnectedSpace M] in
theorem nullOrientationQuotientMap_fiber_eq_orbit (C : NullOrientationCover D)
    (p q : UnitRicciKernel D) :
    nullOrientationQuotientMap C p = nullOrientationQuotientMap C q ↔
      q = p ∨ q = C.deck p :=
  nullOrientationQuotientMap_eq_iff C p q

end PoincareConjecture.RicciFlow.Splitting
