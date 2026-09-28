import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEventRegions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_family_surgery_reindex
    (n : ℕ) (psi : Fin n → UnitTwoSphere × ℝ → E3)
    (hembed : ∀ i : Fin n, IsCollarEmbedding (psi i))
    (hdisjoint : Pairwise (fun i j : Fin n =>
      Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
        (range (fun q : UnitTwoSphere => psi j (q, 0)))))
    (u : UnitTwoSphere) (j : Fin n)
    (E : RegularSurgeryEvent (psi j) u)
    (hothers : ∀ i : Fin n, i ≠ j → ∀ k : Fin 2,
      Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
        (range (fun q : UnitTwoSphere => E.child k (q, 0)))) :
    ∃ e : Fin (n + 1) ≃ ({i : Fin n // i ≠ j} ⊕ Fin 2),
      let psi' : Fin (n + 1) → UnitTwoSphere × ℝ → E3 :=
        fun a => Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1) E.child (e a)
      (∀ a : Fin (n + 1), IsCollarEmbedding (psi' a)) ∧
      Pairwise (fun a b : Fin (n + 1) =>
        Disjoint (range (fun q : UnitTwoSphere => psi' a (q, 0)))
          (range (fun q : UnitTwoSphere => psi' b (q, 0)))) ∧
      (∀ i : {i : Fin n // i ≠ j}, psi' (e.symm (Sum.inl i)) = psi i.1) ∧
      (∀ i : Fin 2, psi' (e.symm (Sum.inr i)) = E.child i) ∧
      (⋃ a : Fin (n + 1), range (fun q : UnitTwoSphere => psi' a (q, 0))) =
        (⋃ i : {i : Fin n // i ≠ j},
          range (fun q : UnitTwoSphere => psi i.1 (q, 0))) ∪
          (range (fun q : UnitTwoSphere => E.child 0 (q, 0)) ∪
            range (fun q : UnitTwoSphere => E.child 1 (q, 0))) := by
  classical
  let J := {i : Fin n // i ≠ j}
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hcard : Fintype.card J = n - 1 := by
    simpa only [J, Fintype.card_fin, Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun i : Fin n => i = j)
  have hsum : Fintype.card (J ⊕ Fin 2) = n + 1 := by
    rw [Fintype.card_sum, hcard, Fintype.card_fin]
    omega
  let e : Fin (n + 1) ≃ (J ⊕ Fin 2) := (Fintype.equivFinOfCardEq hsum).symm
  let f : J ⊕ Fin 2 → UnitTwoSphere × ℝ → E3 :=
    Sum.elim (fun i : J => psi i.1) E.child
  have hzero (g : UnitTwoSphere × ℝ → E3) :
      g '' (univ ×ˢ ({0} : Set ℝ)) = range (fun q : UnitTwoSphere => g (q, 0)) := by
    ext y
    constructor
    · rintro ⟨⟨q, s⟩, hs, rfl⟩
      have hs0 : s = 0 := hs.2
      subst s
      exact mem_range_self q
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hchildren : Disjoint (range (fun q : UnitTwoSphere => E.child 0 (q, 0)))
      (range (fun q : UnitTwoSphere => E.child 1 (q, 0))) := by
    obtain ⟨_, _, _, _, _, h⟩ := E.region_identities
    simpa only [hzero] using h
  have hfembed (a : J ⊕ Fin 2) : IsCollarEmbedding (f a) := by
    cases a with
    | inl i => exact hembed i.1
    | inr i => exact E.child_embedding i
  have hfdis : Pairwise (fun a b : J ⊕ Fin 2 =>
      Disjoint (range (fun q : UnitTwoSphere => f a (q, 0)))
        (range (fun q : UnitTwoSphere => f b (q, 0)))) := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        exact hdisjoint (fun h => hab (congrArg Sum.inl (Subtype.ext h)))
      | inr b => exact hothers a.1 a.2 b
    | inr a =>
      cases b with
      | inl b => exact (hothers b.1 b.2 a).symm
      | inr b =>
        fin_cases a <;> fin_cases b
        · exact False.elim (hab rfl)
        · exact hchildren
        · exact hchildren.symm
        · exact False.elim (hab rfl)
  refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hfembed (e a)
  · intro a b hab
    exact hfdis (fun h => hab (e.injective h))
  · intro i
    change f (e (e.symm (Sum.inl i))) = psi i.1
    rw [e.apply_symm_apply]
    rfl
  · intro i
    change f (e (e.symm (Sum.inr i))) = E.child i
    rw [e.apply_symm_apply]
    rfl
  · ext y
    constructor
    · intro hy
      obtain ⟨a, ha⟩ := mem_iUnion.mp hy
      change y ∈ range (fun q : UnitTwoSphere => f (e a) (q, 0)) at ha
      cases h : e a with
      | inl i =>
        rw [h] at ha
        exact Or.inl (mem_iUnion.mpr ⟨i, ha⟩)
      | inr i =>
        rw [h] at ha
        fin_cases i
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr ha)
    · rintro (hy | hy | hy)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        refine mem_iUnion.mpr ⟨e.symm (Sum.inl i), ?_⟩
        change y ∈ range (fun q : UnitTwoSphere => f (e (e.symm (Sum.inl i))) (q, 0))
        rw [e.apply_symm_apply]
        exact hi
      · refine mem_iUnion.mpr ⟨e.symm (Sum.inr 0), ?_⟩
        change y ∈ range (fun q : UnitTwoSphere => f (e (e.symm (Sum.inr 0))) (q, 0))
        rw [e.apply_symm_apply]
        exact hy
      · refine mem_iUnion.mpr ⟨e.symm (Sum.inr 1), ?_⟩
        change y ∈ range (fun q : UnitTwoSphere => f (e (e.symm (Sum.inr 1))) (q, 0))
        rw [e.apply_symm_apply]
        exact hy

end PoincareConjecture.M25.Topology3D
