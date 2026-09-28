import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCardinality
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCharge
import PoincareConjecture.Proofs.M76.Mathlib.CircularSubsetTopology
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle
import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalEdges











set_option autoImplicit false

open Set

namespace Set




theorem alexanderCurveCount_eq_of_equiv {X ι κ : Type*} [Finite ι] [Finite κ]
    (D : ι → Set X) (F : κ → Set X) (e : ι ≃ κ) (he : ∀ i, D i = F (e i)) :
    alexanderCurveCount D = alexanderCurveCount F := by
  classical
  have hdisj : Pairwise (fun i j => Disjoint (D i) (D j)) ↔
      Pairwise (fun i j => Disjoint (F i) (F j)) := by
    constructor
    · intro h i j hij
      obtain ⟨i, rfl⟩ := e.surjective i
      obtain ⟨j, rfl⟩ := e.surjective j
      rw [← he i, ← he j]
      exact h (fun h => hij (congrArg e h))
    · intro h i j hij
      rw [he i, he j]
      exact h (fun h => hij (e.injective h))
  simp only [alexanderCurveCount, hdisj, Nat.card_congr e]

end Set

namespace Polygon

variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι] [Finite κ]






theorem exists_equiv_of_common_point_section
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (m : κ → ℕ) (Q : ∀ j, Polygon E (m j + 3))
    (hPe : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    (hQe : ∀ j, (Q j).HasSimplicialEdges) (hQi : ∀ j, Function.Injective (Q j))
    (q : E)
    (hpP : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    (hpQ : Pairwise (fun i j => (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ {q}))
    (hcover : {q} ∪ ⋃ i, (P i).boundary ℝ = {q} ∪ ⋃ j, (Q j).boundary ℝ) :
    ∃ e : ι ≃ κ, (∀ i, (P i).boundary ℝ = (Q (e i)).boundary ℝ) ∧
      Nat.card ι = Nat.card κ ∧
      alexanderCurveCount (fun i => (P i).boundary ℝ) =
        alexanderCurveCount (fun j => (Q j).boundary ℝ) := by
  have hpuncP (i : ι) : IsConnected ((P i).boundary ℝ \ {q}) := by
    obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hPe i) (hPi i)
    exact isConnected_sdiff_singleton_of_homeomorph_circle ((P i).boundary ℝ) e q
  have hpuncQ (j : κ) : IsConnected ((Q j).boundary ℝ \ {q}) := by
    obtain ⟨e⟩ := (Q j).nonempty_boundary_homeomorph_circle (hQe j) (hQi j)
    exact isConnected_sdiff_singleton_of_homeomorph_circle ((Q j).boundary ℝ) e q
  have hclP (i : ι) : closure ((P i).boundary ℝ \ {q}) = (P i).boundary ℝ := by
    obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hPe i) (hPi i)
    have hconn : IsConnected ((P i).boundary ℝ) :=
      isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
    exact hconn.isPreconnected.closure_sdiff_singleton_eq
      (P i).isClosed_boundary q (hpuncP i).nonempty
  have hclQ (j : κ) : closure ((Q j).boundary ℝ \ {q}) = (Q j).boundary ℝ := by
    obtain ⟨e⟩ := (Q j).nonempty_boundary_homeomorph_circle (hQe j) (hQi j)
    have hconn : IsConnected ((Q j).boundary ℝ) :=
      isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
    exact hconn.isPreconnected.closure_sdiff_singleton_eq
      (Q j).isClosed_boundary q (hpuncQ j).nonempty
  have hpuncture : (⋃ i, (P i).boundary ℝ \ {q}) = ⋃ j, (Q j).boundary ℝ \ {q} := by
    have h := congrArg (fun s : Set E => s \ {q}) hcover
    simpa only [union_sdiff_distrib, sdiff_self, empty_union, iUnion_sdiff] using h
  obtain ⟨e, he⟩ := exists_equiv_punctured_closed_connected_families
    (fun i => (P i).boundary ℝ) (fun j => (Q j).boundary ℝ)
    (fun i => (P i).isClosed_boundary) (fun j => (Q j).isClosed_boundary)
    q hpuncP hpuncQ hpP hpQ hpuncture
  have hfull (i : ι) : (P i).boundary ℝ = (Q (e i)).boundary ℝ :=
    (hclP i).symm.trans ((congrArg closure (he i)).trans (hclQ (e i)))
  exact ⟨e, hfull, Nat.card_congr e,
    alexanderCurveCount_eq_of_equiv (fun i => (P i).boundary ℝ)
      (fun j => (Q j).boundary ℝ) e hfull⟩

end Polygon
