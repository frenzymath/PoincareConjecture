import PoincareConjecture.Proofs.M76.Mathlib.FiniteSegmentCorrespondence
import PoincareConjecture.Proofs.M76.Mathlib.PolygonPathCycles











set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [Finite ι]






theorem exists_common_simplicial_path_complex
    (n : ι → ℕ) (p : (a : ι) → Fin (n a + 2) → E)
    (hpi : ∀ a, Function.Injective (p a))
    (hself : ∀ a, ∀ i j : Fin (n a + 1),
      segment ℝ (p a i.castSucc) (p a i.succ) ∩
          segment ℝ (p a j.castSucc) (p a j.succ) ⊆
        convexHull ℝ (({p a i.castSucc, p a i.succ} : Set E) ∩
          {p a j.castSucc, p a j.succ}))
    (hvertex : ∀ a, ∀ (i : Fin (n a + 1)) (j : Fin (n a + 2)),
      p a j ∈ segment ℝ (p a i.castSucc) (p a i.succ) →
        p a j = p a i.castSucc ∨ p a j = p a i.succ)
    (hcross : ∀ a b, a ≠ b →
      pathCarrier (p a) ∩ pathCarrier (p b) ⊆ range (p a) ∩ range (p b)) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧
      (∀ (a : ι) (i : Fin (n a + 1)),
        ({p a i.castSucc, p a i.succ} : Finset E) ∈ K.faces) ∧
      K.space = ⋃ a, pathCarrier (p a) := by
  classical
  let I := (a : ι) × Fin (n a + 1)
  let u : I → E := fun i => p i.1 i.2.castSucc
  let v : I → E := fun i => p i.1 i.2.succ
  have hne (i : I) : u i ≠ v i :=
    (hpi i.1).ne (ne_of_lt Fin.castSucc_lt_succ)
  have hinter (i j : I) : segment ℝ (u i) (v i) ∩ segment ℝ (u j) (v j) ⊆
      convexHull ℝ (({u i, v i} : Set E) ∩ {u j, v j}) := by
    rcases i with ⟨a, i⟩
    rcases j with ⟨b, j⟩
    intro x hx
    by_cases hab : a = b
    · subst b
      exact hself a i j hx
    · have hxab : x ∈ pathCarrier (p a) ∩ pathCarrier (p b) :=
        ⟨mem_iUnion.mpr ⟨i, hx.1⟩, mem_iUnion.mpr ⟨j, hx.2⟩⟩
      obtain ⟨hxa, hxb⟩ := hcross a b hab hxab
      obtain ⟨k, hk⟩ := hxa
      obtain ⟨l, hl⟩ := hxb
      apply subset_convexHull ℝ _
      constructor
      · have hk' := hvertex a i k (hk.symm ▸ hx.1)
        simpa only [u, v, hk, mem_insert_iff, mem_singleton_iff] using hk'
      · have hl' := hvertex b j l (hl.symm ▸ hx.2)
        simpa only [u, v, hl, mem_insert_iff, mem_singleton_iff] using hl'
  obtain ⟨K, hK, hfaces, hspace⟩ :=
    SimplicialComplex.exists_finite_segment_complex u v hne hinter
  refine ⟨K, hK, ?_, ?_⟩
  · intro a i
    exact (hfaces _).mpr
      ⟨Finset.insert_nonempty _ _, ⟨a, i⟩, Finset.Subset.refl _⟩
  · simpa only [I, u, v, iUnion_sigma, pathCarrier] using hspace

end Polygon
