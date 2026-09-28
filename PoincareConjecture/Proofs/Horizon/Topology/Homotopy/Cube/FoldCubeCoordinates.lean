import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.CubeSimplexCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.ThreeFaceFold

set_option autoImplicit false

namespace Poincare.Topology

theorem stdSimplex_cube_coordinates_cons (n : Nat)
    (q : C((Fin (n + 1) -> unitInterval), stdSimplex Real (Fin (n + 2))))
    (hq0 : forall t, q t 0 = ∏ k : Fin (n + 1), (1 - (t k : Real)))
    (hqs : forall t (j : Fin (n + 1)), q t j.succ =
      (t j : Real) * ∏ k : Fin (n + 1), if j < k then 1 - (t k : Real) else 1)
    (s : unitInterval) (t : Fin n -> unitInterval) :
    And (q (Fin.cons s t) 0 = (1 - (s : Real)) * ∏ k : Fin n, (1 - (t k : Real)))
      (And (q (Fin.cons s t) 1 = (s : Real) * ∏ k : Fin n, (1 - (t k : Real)))
        (forall (a : unitInterval) (j : Fin n),
          q (Fin.cons s t) j.succ.succ = q (Fin.cons a t) j.succ.succ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hq0, Fin.prod_univ_succ]
    rfl
  · change q (Fin.cons s t) (0 : Fin (n + 1)).succ = _
    rw [hqs, Fin.prod_univ_succ]
    change (s : Real) * ((if (0 : Fin (n + 1)) < 0 then 1 - (s : Real) else 1) *
      ∏ k : Fin n, if 0 < k.succ then 1 - (t k : Real) else 1) = _
    rw [if_neg (lt_irrefl _), one_mul]
    apply congrArg (fun r : Real => (s : Real) * r)
    apply Finset.prod_congr rfl
    intro k _
    exact if_pos k.succ_pos
  · intro a j
    rw [hqs, hqs, Fin.prod_univ_succ, Fin.prod_univ_succ]
    change (t j : Real) * ((if j.succ < 0 then 1 - (s : Real) else 1) *
      ∏ k : Fin n, if j.succ < k.succ then 1 - (t k : Real) else 1) =
      (t j : Real) * ((if j.succ < 0 then 1 - (a : Real) else 1) *
      ∏ k : Fin n, if j.succ < k.succ then 1 - (t k : Real) else 1)
    rw [if_neg (Fin.not_lt_zero _), if_neg (Fin.not_lt_zero _)]

theorem stdSimplex_three_face_fold_cube_first (n : Nat)
    (q : C((Fin (n + 1) -> unitInterval), stdSimplex Real (Fin (n + 2))))
    (hq0 : forall t, q t 0 = ∏ k : Fin (n + 1), (1 - (t k : Real)))
    (hqs : forall t (j : Fin (n + 1)), q t j.succ =
      (t j : Real) * ∏ k : Fin (n + 1), if j < k then 1 - (t k : Real) else 1)
    (w : C(stdSimplex Real (Fin (n + 2)), stdSimplex Real (Fin (n + 3))))
    (hw0 : forall z, w z 0 = z 0 - min (z 0) (z 1))
    (hw1 : forall z, w z 1 = 2 * min (z 0) (z 1))
    (hw2 : forall z, w z 2 = z 1 - min (z 0) (z 1))
    (hws : forall z (j : Fin n), w z j.succ.succ.succ = z j.succ.succ)
    (s a : unitInterval) (t : Fin n -> unitInterval)
    (ha : (a : Real) = 2 * (s : Real)) :
    w (q (Fin.cons s t)) =
      stdSimplex.map (2 : Fin (n + 3)).succAbove (q (Fin.cons a t)) := by
  obtain ⟨hs0, hs1, htail⟩ := stdSimplex_cube_coordinates_cons n q hq0 hqs s t
  obtain ⟨ha0, ha1, _⟩ := stdSimplex_cube_coordinates_cons n q hq0 hqs a t
  let r : Real := ∏ k : Fin n, (1 - (t k : Real))
  have hr : 0 ≤ r := Finset.prod_nonneg (fun k _ => sub_nonneg.mpr (t k).property.2)
  have hs : (s : Real) ≤ 1 - (s : Real) := by
    apply (le_sub_iff_add_le).mpr
    rw [← two_mul, ← ha]
    exact a.property.2
  have hmin : min (q (Fin.cons s t) 0) (q (Fin.cons s t) 1) = (s : Real) * r := by
    rw [hs0, hs1]
    exact min_eq_right (mul_le_mul_of_nonneg_right hs hr)
  have hf0 : stdSimplex.map (2 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 0 =
      q (Fin.cons a t) 0 := stdSimplex_face_succAbove (n + 1) 2 (q (Fin.cons a t)) 0
  have hf1 : stdSimplex.map (2 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 1 =
      q (Fin.cons a t) 1 := stdSimplex_face_succAbove (n + 1) 2 (q (Fin.cons a t)) 1
  have hftail (j : Fin n) :
      stdSimplex.map (2 : Fin (n + 3)).succAbove (q (Fin.cons a t)) j.succ.succ.succ =
        q (Fin.cons a t) j.succ.succ := by
    have hi : (2 : Fin (n + 3)).succAbove j.succ.succ = j.succ.succ.succ := by
      rw [← Fin.succ_one_eq_two]
      apply Fin.succAbove_succ_of_lt
      change (0 : Fin (n + 1)).succ < j.succ.succ
      exact Fin.succ_lt_succ_iff.mpr (Fin.succ_pos _)
    have h := stdSimplex_face_succAbove (n + 1) 2 (q (Fin.cons a t)) j.succ.succ
    rw [hi] at h
    exact h
  apply Subtype.ext
  funext k
  refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun m => Fin.cases ?_ (fun j => ?_) m) l) k
  · change w (q (Fin.cons s t)) 0 =
      stdSimplex.map (2 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 0
    rw [hw0, hmin, hs0, hf0, ha0, ha]
    change (1 - (s : Real)) * r - (s : Real) * r = (1 - 2 * (s : Real)) * r
    ring
  · change w (q (Fin.cons s t)) 1 =
      stdSimplex.map (2 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 1
    rw [hw1, hmin, hf1, ha1, ha]
    exact (mul_assoc _ _ _).symm
  · change w (q (Fin.cons s t)) 2 =
      stdSimplex.map (2 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 2
    rw [hw2, hmin, hs1, stdSimplex_face_zero]
    exact sub_self _
  · exact (hws _ j).trans ((htail a j).trans (hftail j).symm)

theorem stdSimplex_three_face_fold_cube_second (n : Nat)
    (q : C((Fin (n + 1) -> unitInterval), stdSimplex Real (Fin (n + 2))))
    (hq0 : forall t, q t 0 = ∏ k : Fin (n + 1), (1 - (t k : Real)))
    (hqs : forall t (j : Fin (n + 1)), q t j.succ =
      (t j : Real) * ∏ k : Fin (n + 1), if j < k then 1 - (t k : Real) else 1)
    (w : C(stdSimplex Real (Fin (n + 2)), stdSimplex Real (Fin (n + 3))))
    (hw0 : forall z, w z 0 = z 0 - min (z 0) (z 1))
    (hw1 : forall z, w z 1 = 2 * min (z 0) (z 1))
    (hw2 : forall z, w z 2 = z 1 - min (z 0) (z 1))
    (hws : forall z (j : Fin n), w z j.succ.succ.succ = z j.succ.succ)
    (s a : unitInterval) (t : Fin n -> unitInterval)
    (ha : (a : Real) = 2 * (s : Real) - 1) :
    w (q (Fin.cons s t)) =
      stdSimplex.map (0 : Fin (n + 3)).succAbove (q (Fin.cons a t)) := by
  obtain ⟨hs0, hs1, htail⟩ := stdSimplex_cube_coordinates_cons n q hq0 hqs s t
  obtain ⟨ha0, ha1, _⟩ := stdSimplex_cube_coordinates_cons n q hq0 hqs a t
  let r : Real := ∏ k : Fin n, (1 - (t k : Real))
  have hr : 0 ≤ r := Finset.prod_nonneg (fun k _ => sub_nonneg.mpr (t k).property.2)
  have hs : 1 - (s : Real) ≤ (s : Real) := by
    apply (sub_le_iff_le_add).mpr
    rw [← two_mul]
    apply sub_nonneg.mp
    rw [← ha]
    exact a.property.1
  have hmin : min (q (Fin.cons s t) 0) (q (Fin.cons s t) 1) = (1 - (s : Real)) * r := by
    rw [hs0, hs1]
    exact min_eq_left (mul_le_mul_of_nonneg_right hs hr)
  have hf1 : stdSimplex.map (0 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 1 =
      q (Fin.cons a t) 0 := stdSimplex_face_succAbove (n + 1) 0 (q (Fin.cons a t)) 0
  have hf2 : stdSimplex.map (0 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 2 =
      q (Fin.cons a t) 1 := stdSimplex_face_succAbove (n + 1) 0 (q (Fin.cons a t)) 1
  have hftail (j : Fin n) :
      stdSimplex.map (0 : Fin (n + 3)).succAbove (q (Fin.cons a t)) j.succ.succ.succ =
        q (Fin.cons a t) j.succ.succ :=
    stdSimplex_face_succAbove (n + 1) 0 (q (Fin.cons a t)) j.succ.succ
  apply Subtype.ext
  funext k
  refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun m => Fin.cases ?_ (fun j => ?_) m) l) k
  · change w (q (Fin.cons s t)) 0 =
      stdSimplex.map (0 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 0
    rw [hw0, hmin, hs0, stdSimplex_face_zero]
    exact sub_self _
  · change w (q (Fin.cons s t)) 1 =
      stdSimplex.map (0 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 1
    rw [hw1, hmin, hf1, ha0, ha]
    change 2 * ((1 - (s : Real)) * r) = (1 - (2 * (s : Real) - 1)) * r
    ring
  · change w (q (Fin.cons s t)) 2 =
      stdSimplex.map (0 : Fin (n + 3)).succAbove (q (Fin.cons a t)) 2
    rw [hw2, hmin, hs1, hf2, ha1, ha]
    change (s : Real) * r - (1 - (s : Real)) * r = (2 * (s : Real) - 1) * r
    ring
  · exact (hws _ j).trans ((htail a j).trans (hftail j).symm)

end Poincare.Topology
