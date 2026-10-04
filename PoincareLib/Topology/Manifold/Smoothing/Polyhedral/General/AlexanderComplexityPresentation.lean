import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.AlexanderComplexityCardinalityPolygons

/-!
# Geometric witnesses for a section's Alexander charge

A presentation records actual simple polygons, at most one residue
point, exact coverage and the common-point intersection bound. Finite
index reparametrization preserves the charge. See Alexander 1924,
pp. 6--8 and M76 derivation 246.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A literal section carrier has this charge through a complete
finite simple-polygon presentation with at most one residue point.
This predicate supplies geometric witnesses rather than assuming a
topological classification. See Alexander p. 6 and derivation 246. -/
def HasAlexanderCurvePresentation (s : Set E) (a : ℕ) : Prop :=
  ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)) (r : Set E),
    (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
    r.Subsingleton ∧ s = r ∪ ⋃ i, (P i).boundary ℝ ∧
    Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ r) ∧
    alexanderCurveCount (fun i => (P i).boundary ℝ) = a

/-- Any complete finite indexed polygon family supplies a
presentation with its actual charge. Reindexing changes neither
the carrier nor the incidence relation. See Alexander pp. 6--8
and derivation 246. -/
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
