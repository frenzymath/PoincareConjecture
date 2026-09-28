import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Operations
import Mathlib.LinearAlgebra.Multilinear.Basic

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup E] [Module ℝ E]






lemma slot_double_sum_sub
    (A : MultilinearMap ℝ (fun _ : ι => E) ℝ)
    (v B C D E' : ι → E) :
    (∑ i, ∑ j, A (Function.update (Function.update v i (B i)) j
      (if j = i then D i else C j))) -
      ∑ i, ∑ j, A (Function.update (Function.update v i (C i)) j
        (if j = i then E' i else B j)) =
      ∑ i, A (Function.update v i (D i - E' i)) := by
  classical
  let f : ι → ι → ℝ := fun i j ↦
    A (Function.update (Function.update v i (B i)) j (C j))
  let g : ι → ι → ℝ := fun i j ↦
    A (Function.update (Function.update v i (C i)) j (B j))
  have hdiag₁ (i : ι) :
      A (Function.update (Function.update v i (B i)) i (D i)) =
        A (Function.update v i (D i)) := by
    simp
  have hdiag₂ (i : ι) :
      A (Function.update (Function.update v i (C i)) i (E' i)) =
        A (Function.update v i (E' i)) := by
    simp
  have hoff (i j : ι) (hij : i ≠ j) : g i j = f j i := by
    dsimp [f, g]
    rw [Function.update_comm hij]
  have hsum_off :
      (∑ i, ∑ j, if j = i then 0 else f i j) =
        ∑ i, ∑ j, if j = i then 0 else g i j := by
    calc
      (∑ i, ∑ j, if j = i then 0 else f i j) =
          ∑ i, ∑ j, if i = j then 0 else f i j := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            by_cases h : j = i
            · simp [h]
            · have h' : i ≠ j := Ne.symm h
              simp [h, h']
      _ = ∑ j, ∑ i, if i = j then 0 else f i j := by
            rw [Finset.sum_comm]
      _ = ∑ j, ∑ i, if i = j then 0 else g j i := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h : i = j
            · simp [h]
            · have h' : j ≠ i := Ne.symm h
              simp only [h, ↓reduceIte]
              exact (hoff j i h').symm
      _ = ∑ i, ∑ j, if j = i then 0 else g i j := by
            simpa only [eq_comm] using
              (Finset.sum_comm (s := (Finset.univ : Finset ι))
                (t := (Finset.univ : Finset ι))
                (f := fun j i ↦ if i = j then 0 else g j i))
  have hsum_diag :
      (∑ i, (A (Function.update v i (D i)) -
        A (Function.update v i (E' i)))) =
        ∑ i, A (Function.update v i (D i - E' i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [A.map_update_sub]
  have hsplit₁ (i : ι) :
      (∑ j, A (Function.update (Function.update v i (B i)) j
        (if j = i then D i else C j))) =
        A (Function.update v i (D i)) + ∑ j, if j = i then 0 else f i j := by
    calc
      _ = ∑ j, ((if j = i then A (Function.update v i (D i)) else 0) +
          (if j = i then 0 else f i j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases h : j = i
            · simp [h, hdiag₁]
            · simp [h, f]
      _ = (∑ j, if j = i then A (Function.update v i (D i)) else 0) +
          ∑ j, if j = i then 0 else f i j := by rw [Finset.sum_add_distrib]
      _ = _ := by simp
  have hsplit₂ (i : ι) :
      (∑ j, A (Function.update (Function.update v i (C i)) j
        (if j = i then E' i else B j))) =
        A (Function.update v i (E' i)) + ∑ j, if j = i then 0 else g i j := by
    calc
      _ = ∑ j, ((if j = i then A (Function.update v i (E' i)) else 0) +
          (if j = i then 0 else g i j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases h : j = i
            · simp [h, hdiag₂]
            · simp [h, g]
      _ = (∑ j, if j = i then A (Function.update v i (E' i)) else 0) +
          ∑ j, if j = i then 0 else g i j := by rw [Finset.sum_add_distrib]
      _ = _ := by simp
  simp_rw [hsplit₁, hsplit₂]
  calc
    _ = (∑ i, A (Function.update v i (D i)) -
          ∑ i, A (Function.update v i (E' i))) +
        ((∑ i, ∑ j, if j = i then 0 else f i j) -
          ∑ i, ∑ j, if j = i then 0 else g i j) := by
      simp only [Finset.sum_add_distrib]
      ring
    _ = ∑ i, A (Function.update v i (D i)) -
          ∑ i, A (Function.update v i (E' i)) := by
      rw [hsum_off]
      ring
    _ = _ := by rw [← Finset.sum_sub_distrib, hsum_diag]

end PoincareConjecture
