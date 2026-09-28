import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import Mathlib.Analysis.Convex.PathConnected










set_option autoImplicit false

open Set

namespace AffineIndependent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem isConnected_intrinsicFrontier_convexHull_finset
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) (hcard : 3 ≤ s.card) :
    IsConnected (intrinsicFrontier ℝ (convexHull ℝ (s : Set E))) := by
  classical
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  let : Nonempty s := hsne.to_subtype
  have hfront : intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) =
      ⋃ i : s, convexHull ℝ ((s.erase i : Finset E) : Set E) := by
    ext x
    rw [hs.mem_intrinsicFrontier_convexHull_finset hsne x]
    simp only [mem_iUnion, Subtype.exists, exists_prop]
  have hconn (i : s) : IsConnected (convexHull ℝ ((s.erase i : Finset E) : Set E)) := by
    have hne : (s.erase (i : E)).Nonempty := by
      have hc := Finset.card_erase_of_mem i.property
      exact Finset.card_pos.mp (by omega)
    exact (convex_convexHull ℝ _).isConnected
      (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hne))
  have hmeet (i j : s) :
      (convexHull ℝ ((s.erase i : Finset E) : Set E) ∩
        convexHull ℝ ((s.erase j : Finset E) : Set E)).Nonempty := by
    have hpair : ({(i : E), (j : E)} : Finset E).card ≤ 2 := by
      rcases Finset.card_pair_eq_one_or_two (a := (i : E)) (b := (j : E)) with h | h <;> omega
    obtain ⟨v, hv, hvnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show ({(i : E), (j : E)} : Finset E).card < s.card by omega)
    have hvi : v ≠ (i : E) := by
      intro h
      exact hvnot (by simp [h])
    have hvj : v ≠ (j : E) := by
      intro h
      exact hvnot (by simp [h])
    exact ⟨v, subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hvi, hv⟩),
      subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hvj, hv⟩)⟩
  rw [hfront]
  exact IsConnected.iUnion_of_reflTransGen hconn
    (fun i j => Relation.ReflTransGen.single (hmeet i j))

end AffineIndependent
