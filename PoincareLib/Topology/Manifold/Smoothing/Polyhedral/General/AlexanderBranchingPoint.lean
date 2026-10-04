import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonBranchingPoint
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.IntrinsicBranchingSection

/-!
# Positive child presentations retain the original branching point

The exact child-section inclusion, together with the actual
source family, identifies the marked point of any chosen
positive-charge child presentation. No charge invariance or
common choice of polygon witnesses is assumed. See Alexander
1924, pp. 6--8 and M76 derivations 269 and 274.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

/-- A positive-charge presentation on any subset of a
complete source polygon family has an actual full branching
family at the original marked point. Its count remains the
given charge of that same child presentation.
See Alexander pp. 6--8 and M76 derivation 274. -/
theorem HasAlexanderCurvePresentation.exists_branching_family_at_common_point
    {S T r : Set E} {a : ℕ} (h : HasAlexanderCurvePresentation T a)
    (ha : a ≠ 0) (hTS : T ⊆ S)
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    {q : E} (hr : r ⊆ {q}) (hcover : S = r ∪ ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q})) :
    ∃ (m : ℕ) (N : Fin m → ℕ) (Q : ∀ i, Polygon E (N i + 3)),
      0 < m ∧
      (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges) ∧
      T = ⋃ i, (Q i).boundary ℝ ∧
      Pairwise (fun i j => (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ {q}) ∧
      (¬ Pairwise (fun i j => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ))) ∧
      alexanderCurveCount (fun i => (Q i).boundary ℝ) = a ∧
      q ∈ T ∧ q ∈ closure (T \ {q}) := by
  obtain ⟨m, N, Q, p, hm, hQ, hfull, hQpair, hbranch, hcount, hpT, hacc⟩ :=
    h.exists_branching_family ha
  have hQS (i : Fin m) : (Q i).boundary ℝ ⊆ S :=
    fun x hx => hTS (hfull.symm.subset (mem_iUnion.mpr ⟨i, hx⟩))
  have hpq : p = q := Polygon.common_point_eq_of_branching_family_subset
    n P hP hr hcover hpair N Q hQ hQS hQpair hbranch
  subst p
  exact ⟨m, N, Q, hm, hQ, hfull, hQpair, hbranch, hcount, hpT, hacc⟩

end Set
