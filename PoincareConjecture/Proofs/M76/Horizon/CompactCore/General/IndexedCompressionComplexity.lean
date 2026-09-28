import PoincareConjecture.Proofs.M76.Wall.CompressionComplexity
import Mathlib.Algebra.BigOperators.Fin










set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M76.Wall

theorem compressionComplexity_finRange_eq_sum {n : ℕ} (genus : Fin n → ℕ) :
    compressionComplexity ((List.finRange n).map genus) =
      ∑ i, (2 * genus i - 1) := by
  rw [compressionComplexity, List.map_map, ← Fin.sum_univ_def]
  rfl

private theorem sum_eq_selected_add_complement {n : ℕ} (f : Fin n → ℕ) (a : Fin n) :
    ∑ i, f i = f a + ∑ i : {i : Fin n // i ≠ a}, f i := by
  classical
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  rw [Finset.sum_subtype (p := fun i => i ≠ a) _ (by simp) f] at h
  omega

private theorem sum_eq_two_selected_add_complement {n : ℕ} (f : Fin n → ℕ)
    (a b : Fin n) (hab : a ≠ b) :
    ∑ i, f i = f a + f b + ∑ i : {i : Fin n // i ≠ a ∧ i ≠ b}, f i := by
  classical
  have h1 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  have h2 := Finset.sum_erase_add (Finset.univ.erase a) f
    (show b ∈ Finset.univ.erase a by simp [hab.symm])
  rw [Finset.sum_subtype (p := fun i => i ≠ a ∧ i ≠ b) _
    (by simp [and_comm]) f] at h2
  omega

theorem compressionComplexity_indexed_nonseparating
    {n m : ℕ} (oldGenus : Fin n → ℕ) (newGenus : Fin m → ℕ)
    (oldLabel : Fin n) (newLabel : Fin m)
    (same : {i : Fin n // i ≠ oldLabel} ≃ {k : Fin m // k ≠ newLabel})
    (hSame : ∀ i : {i : Fin n // i ≠ oldLabel}, oldGenus i = newGenus (same i))
    (hgenus : oldGenus oldLabel = newGenus newLabel + 1) :
    compressionComplexity ((List.finRange m).map newGenus) <
      compressionComplexity ((List.finRange n).map oldGenus) := by
  have hrest := Fintype.sum_equiv same
    (fun i => 2 * oldGenus i - 1) (fun k => 2 * newGenus k - 1)
    (fun i => by rw [hSame i])
  rw [compressionComplexity_finRange_eq_sum, compressionComplexity_finRange_eq_sum,
    sum_eq_selected_add_complement _ newLabel, sum_eq_selected_add_complement _ oldLabel]
  omega

theorem compressionComplexity_indexed_separating
    {n m : ℕ} (oldGenus : Fin n → ℕ) (newGenus : Fin m → ℕ)
    (oldLabel : Fin n) (leftLabel rightLabel : Fin m) (hne : leftLabel ≠ rightLabel)
    (same : {i : Fin n // i ≠ oldLabel} ≃
      {k : Fin m // k ≠ leftLabel ∧ k ≠ rightLabel})
    (hSame : ∀ i : {i : Fin n // i ≠ oldLabel}, oldGenus i = newGenus (same i))
    (hleft : 0 < newGenus leftLabel) (hright : 0 < newGenus rightLabel)
    (hgenus : oldGenus oldLabel = newGenus leftLabel + newGenus rightLabel) :
    compressionComplexity ((List.finRange m).map newGenus) <
      compressionComplexity ((List.finRange n).map oldGenus) := by
  have hrest := Fintype.sum_equiv same
    (fun i => 2 * oldGenus i - 1) (fun k => 2 * newGenus k - 1)
    (fun i => by rw [hSame i])
  rw [compressionComplexity_finRange_eq_sum, compressionComplexity_finRange_eq_sum,
    sum_eq_two_selected_add_complement _ leftLabel rightLabel hne,
    sum_eq_selected_add_complement _ oldLabel]
  omega

private theorem int_sum_eq_selected_add_complement {n : ℕ} (f : Fin n → ℤ) (a : Fin n) :
    ∑ i, f i = f a + ∑ i : {i : Fin n // i ≠ a}, f i := by
  classical
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  rw [Finset.sum_subtype (p := fun i => i ≠ a) _ (by simp) f] at h
  omega

private theorem int_sum_eq_two_selected_add_complement {n : ℕ} (f : Fin n → ℤ)
    (a b : Fin n) (hab : a ≠ b) :
    ∑ i, f i = f a + f b + ∑ i : {i : Fin n // i ≠ a ∧ i ≠ b}, f i := by
  classical
  have h1 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  have h2 := Finset.sum_erase_add (Finset.univ.erase a) f
    (show b ∈ Finset.univ.erase a by simp [hab.symm])
  rw [Finset.sum_subtype (p := fun i => i ≠ a ∧ i ≠ b) _
    (by simp [and_comm]) f] at h2
  omega



theorem compressionComplexity_indexed_of_euler_change
    {n m : ℕ} (oldGenus : Fin n → ℕ) (newGenus : Fin m → ℕ)
    (oldLabel : Fin n) (capLabel : Bool → Fin m)
    (same : {i : Fin n // i ≠ oldLabel} ≃
      {k : Fin m // k ≠ capLabel false ∧ k ≠ capLabel true})
    (hSame : ∀ i : {i : Fin n // i ≠ oldLabel}, oldGenus i = newGenus (same i))
    (hpositive : capLabel false ≠ capLabel true → ∀ b, 0 < newGenus (capLabel b))
    (hEuler : (∑ k, (2 - 2 * (newGenus k : ℤ))) =
      (∑ i, (2 - 2 * (oldGenus i : ℤ))) + 2) :
    compressionComplexity ((List.finRange m).map newGenus) <
      compressionComplexity ((List.finRange n).map oldGenus) := by
  classical
  by_cases hcaps : capLabel false = capLabel true
  · let collapse : {k : Fin m // k ≠ capLabel false ∧ k ≠ capLabel true} ≃
        {k : Fin m // k ≠ capLabel false} :=
      Equiv.subtypeEquivRight (fun k => by rw [← hcaps]; exact and_self_iff)
    let single := same.trans collapse
    have hsingle (i : {i : Fin n // i ≠ oldLabel}) :
        oldGenus i = newGenus (single i) := hSame i
    have hrest := Fintype.sum_equiv single
      (fun i => 2 - 2 * (oldGenus i : ℤ))
      (fun k => 2 - 2 * (newGenus k : ℤ)) (fun i => by rw [hsingle i])
    rw [int_sum_eq_selected_add_complement _ (capLabel false),
      int_sum_eq_selected_add_complement _ oldLabel] at hEuler
    apply compressionComplexity_indexed_nonseparating oldGenus newGenus oldLabel
      (capLabel false) single hsingle
    omega
  · have hrest := Fintype.sum_equiv same
      (fun i => 2 - 2 * (oldGenus i : ℤ))
      (fun k => 2 - 2 * (newGenus k : ℤ)) (fun i => by rw [hSame i])
    rw [int_sum_eq_two_selected_add_complement _ (capLabel false) (capLabel true) hcaps,
      int_sum_eq_selected_add_complement _ oldLabel] at hEuler
    apply compressionComplexity_indexed_separating oldGenus newGenus oldLabel
      (capLabel false) (capLabel true) hcaps same hSame
      (hpositive hcaps false) (hpositive hcaps true)
    omega

end PoincareConjecture.M76.Wall
