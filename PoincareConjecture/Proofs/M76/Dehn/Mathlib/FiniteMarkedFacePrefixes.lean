import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteMarkedFaceOrder
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_finite_marked_face_prefixes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    {n : ℕ} (f : Fin n → Finset E) (hfaces : range f = K.faces)
    (hbefore : ∀ i j, f j ⊂ f i → j < i)
    (hphase : ∀ i j, j < i → f i ∈ A.faces → f j ∈ A.faces) :
    ∃ P : ℕ → SimplicialComplex ℝ E,
      (∀ k, (P k).faces.Finite ∧ P k ≤ K ∧
        (P k).faces = {σ | ∃ i : Fin n, i.val < k ∧ f i = σ} ∧
        (P k).space = ⋃ i : Fin n, ⋃ (_ : i.val < k), convexHull ℝ (f i : Set E)) ∧
      (P 0).space = ∅ ∧ (P n).space = K.space ∧
      ∀ i : Fin n,
        (P (i.val + 1)).space = (P i.val).space ∪ convexHull ℝ (f i : Set E) ∧
        (f i ∈ A.faces → P i.val ≤ A) ∧
        (f i ∉ A.faces → A ≤ P i.val) := by
  have hface (i : Fin n) : f i ∈ K.faces := hfaces.subset ⟨i, rfl⟩
  let P (k : ℕ) : SimplicialComplex ℝ E :=
    { faces := {σ | σ ∈ K.faces ∧ ∃ i : Fin n, i.val < k ∧ f i = σ}
      indep := fun hσ => K.indep hσ.1
      isRelLowerSet_faces := by
        intro σ hσ
        refine ⟨K.nonempty_of_mem_faces hσ.1, ?_⟩
        intro τ hτσ hτ
        have hτK : τ ∈ K.faces := K.down_closed hσ.1 hτσ hτ
        refine ⟨hτK, ?_⟩
        obtain ⟨i, hi, rfl⟩ := hσ.2
        by_cases heq : τ = f i
        · exact ⟨i, hi, heq.symm⟩
        · obtain ⟨j, rfl⟩ := hfaces.symm.subset hτK
          have hji : j < i := hbefore i j
            (Finset.ssubset_iff_subset_ne.mpr ⟨hτσ, heq⟩)
          exact ⟨j, lt_trans hji hi, rfl⟩
      inter_subset_convexHull := fun hσ hτ => K.inter_subset_convexHull hσ.1 hτ.1 }
  have hPK (k : ℕ) : P k ≤ K := fun _ hσ => hσ.1
  have hPf (k : ℕ) : (P k).faces = {σ | ∃ i : Fin n, i.val < k ∧ f i = σ} := by
    ext σ
    constructor
    · exact fun hσ => hσ.2
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hface i, i, hi, rfl⟩
  have hPs (k : ℕ) :
      (P k).space = ⋃ i : Fin n, ⋃ (_ : i.val < k), convexHull ℝ (f i : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨σ, hσ, hxσ⟩ := mem_space_iff.mp hx
      obtain ⟨i, hi, rfl⟩ := hσ.2
      exact mem_iUnion₂.mpr ⟨i, hi, hxσ⟩
    · intro hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_space_iff.mpr ⟨f i, ⟨hface i, i, hi, rfl⟩, hxi⟩
  refine ⟨P, fun k => ⟨hK.subset (hPK k), hPK k, hPf k, hPs k⟩, ?_, ?_, ?_⟩
  · simp only [hPs, Nat.not_lt_zero, iUnion_of_empty, iUnion_empty]
  · apply le_antisymm (space_subset_of_le (hPK n))
    intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := mem_space_iff.mp hx
    obtain ⟨i, rfl⟩ := hfaces.symm.subset hσ
    exact mem_space_iff.mpr ⟨f i, ⟨hface i, i, i.isLt, rfl⟩, hxσ⟩
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · rw [hPs, hPs]
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        by_cases hji : j.val < i.val
        · exact Or.inl (mem_iUnion₂.mpr ⟨j, hji, hxj⟩)
        · have hji' : j = i := Fin.ext (by omega)
          exact Or.inr (hji' ▸ hxj)
      · rintro (hx | hx)
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
          exact mem_iUnion₂.mpr ⟨j, by omega, hxj⟩
        · exact mem_iUnion₂.mpr ⟨i, Nat.lt_succ_self _, hx⟩
    · intro hiA σ hσ
      obtain ⟨j, hj, rfl⟩ := hσ.2
      exact hphase i j hj hiA
    · intro hiA σ hσ
      obtain ⟨j, rfl⟩ := hfaces.symm.subset (hAK hσ)
      refine ⟨hface j, j, ?_, rfl⟩
      by_contra hj
      rcases lt_or_eq_of_le (le_of_not_gt hj) with hij | hij
      · exact hiA (hphase j i hij hσ)
      · exact hiA ((congrArg f (Fin.ext hij)).symm ▸ hσ)

end Geometry.SimplicialComplex
