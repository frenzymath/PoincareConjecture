import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalSliceCarrier
import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalSliceDegrees
import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalSliceIntersections
import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalGraphPolygons
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCharge











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem exists_exceptionalSlice_polygons_with_zero_degree [DecidableEq E]
    (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) {q : E} (hq : q ∈ K.vertices)
    (hAq : A q = 0) (hzero : ∀ v ∈ K.vertices, A v = 0 → v = q)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)),
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
      K.space ∩ {x | A x = 0} = {q} ∪ ⋃ i, (P i).boundary ℝ ∧
      Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}) ∧
      (alexanderCurveCount (fun i => (P i).boundary ℝ) = 0 →
        ((K.exceptionalSliceGraph A q).neighborSet none).ncard = 0 ∨
          ((K.exceptionalSliceGraph A q).neighborSet none).ncard = 2) := by
  classical
  let := (K.finite_strictCrossingEdges A hK).fintype
  have hco : ∀ e ∈ K.faces, A.StraddlesZero e →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2 :=
    fun e he heA => hcofaces e he (AffineMap.StraddlesZero.card A heA)
  obtain ⟨m, n, P, hP, hcover, hpair, hcycles⟩ :=
    (K.exceptionalSliceGraph A q).exists_polygons_of_exceptional_degrees_with_cycle_recognition
      (K.exceptionalCrossingPoint A q) none
      (by
        intro v hv
        cases v with
        | none => exact (hv rfl).elim
        | some e => exact K.exceptionalSliceGraph_two_neighbors A hAq hzero hco e)
      (K.exceptionalSliceGraph_even_neighbors A hK hAq hzero hco)
      (K.exceptionalCrossingPoint_injective A hq)
      (fun {_ _ _ _} hab hcd => K.exceptionalSliceGraph_segment_inter A hAq hab hcd)
  refine ⟨m, n, P, hP, ?_, hpair, ?_⟩
  · rw [K.exceptionalSliceGraph_carrier A hq hAq hzero hpure, hcover]
  · intro hz
    exact (hcycles ((alexanderCurveCount_eq_zero_iff _).mp hz)).ncard_neighbors_eq_zero_or_two none





theorem exists_exceptionalSlice_polygons (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) {q : E} (hq : q ∈ K.vertices)
    (hAq : A q = 0) (hzero : ∀ v ∈ K.vertices, A v = 0 → v = q)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)),
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
      K.space ∩ {x | A x = 0} = {q} ∪ ⋃ i, (P i).boundary ℝ ∧
      Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}) := by
  classical
  obtain ⟨m, n, P, hP, hcover, hpair, _⟩ :=
    K.exists_exceptionalSlice_polygons_with_zero_degree A hK hq hAq hzero hpure hcofaces
  exact ⟨m, n, P, hP, hcover, hpair⟩

end Geometry.SimplicialComplex
