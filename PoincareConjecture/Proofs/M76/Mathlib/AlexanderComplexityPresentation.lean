import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCardinalityPolygons










set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





def HasAlexanderCurvePresentation (s : Set E) (a : ℕ) : Prop :=
  ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)) (r : Set E),
    (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
    r.Subsingleton ∧ s = r ∪ ⋃ i, (P i).boundary ℝ ∧
    Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ r) ∧
    alexanderCurveCount (fun i => (P i).boundary ℝ) = a





theorem hasAlexanderCurvePresentation_of_family {ι : Type*} [Finite ι]
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    {s r : Set E} (hr : r.Subsingleton)
    (hcover : s = r ∪ ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ r)) :
    HasAlexanderCurvePresentation s (alexanderCurveCount (fun i => (P i).boundary ℝ)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun i => n (e i), fun i => P (e i), r,
    fun i => hP (e i), hr, ?_, ?_, ?_⟩
  · change s = r ∪ ⋃ i : Fin (Fintype.card ι), (P (e i)).boundary ℝ
    rw [e.surjective.iUnion_comp (fun i => (P i).boundary ℝ)]
    exact hcover
  · intro i j hij
    exact hpair (fun h => hij (e.injective h))
  · exact alexanderCurveCount_eq_of_equiv
      (fun i : Fin (Fintype.card ι) => (P (e i)).boundary ℝ)
      (fun i => (P i).boundary ℝ) e (fun _ => rfl)

end Set
