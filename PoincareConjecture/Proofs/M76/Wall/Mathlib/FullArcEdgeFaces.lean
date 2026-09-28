import PoincareConjecture.Proofs.M76.Wall.Mathlib.EdgeChainFaces










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex





theorem pair_mem_faces_iff_of_full_edge_chain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    {n : ℕ} (p : Fin (n + 2) → E) (hinj : Function.Injective p)
    (hverts : ∀ i, p i ∈ A.vertices)
    (hedge : ∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ A.faces)
    (hcover : A.space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ))
    {i j : Fin (n + 2)} (hne : i ≠ j) :
    {p i, p j} ∈ K.faces ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  constructor
  · intro hs
    have hsA : {p i, p j} ∈ A.faces := hfull _ hs (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hverts i
      · rcases Finset.mem_singleton.mp hx with rfl
        exact hverts j)
    obtain ⟨_, k, hsub⟩ := (A.faces_of_edge_chain_cover p hedge hcover _).mp hsA
    have hi : i = k.castSucc ∨ i = k.succ := by
      have h := hsub (Finset.mem_insert_self (p i) {p j})
      simpa only [Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff] using h
    have hj : j = k.castSucc ∨ j = k.succ := by
      have h := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self (p j)))
      simpa only [Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff] using h
    rcases hi with rfl | rfl
    · rcases hj with rfl | rfl
      · exact False.elim (hne rfl)
      · exact Or.inl rfl
    · rcases hj with rfl | rfl
      · exact Or.inr rfl
      · exact False.elim (hne rfl)
  · rintro (hij | hji)
    · let k : Fin (n + 1) := ⟨i.val, by have hj := j.isLt; omega⟩
      have hi : k.castSucc = i := Fin.ext rfl
      have hj : k.succ = j := Fin.ext hij
      simpa only [hi, hj] using hAK (hedge k)
    · let k : Fin (n + 1) := ⟨j.val, by have hi := i.isLt; omega⟩
      have hj : k.castSucc = j := Fin.ext rfl
      have hi : k.succ = i := Fin.ext hji
      simpa only [hi, hj, Finset.pair_comm (p j) (p i)] using hAK (hedge k)

end Geometry.SimplicialComplex
