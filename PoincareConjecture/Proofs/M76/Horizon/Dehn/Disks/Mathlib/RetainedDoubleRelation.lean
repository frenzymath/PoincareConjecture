import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Set.Image

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn

noncomputable def joinSourceCopies {E Y : Type*} {A B : Set E}
    (hAB : Disjoint A B) (jA : A → Y) (jB : B → Y) : (A ∪ B : Set E) → Y := by
  classical
  exact Sum.elim jA jB ∘ Equiv.Set.union hAB

theorem joinSourceCopies_left {E Y : Type*} {A B : Set E}
    (hAB : Disjoint A B) (jA : A → Y) (jB : B → Y) (x : (A ∪ B : Set E)) (hx : (x : E) ∈ A) :
    joinSourceCopies hAB jA jB x = jA ⟨x, hx⟩ := by
  classical
  simp only [joinSourceCopies, Function.comp_apply, Equiv.Set.union_apply_left hAB hx,
    Sum.elim_inl]

theorem joinSourceCopies_right {E Y : Type*} {A B : Set E}
    (hAB : Disjoint A B) (jA : A → Y) (jB : B → Y) (x : (A ∪ B : Set E)) (hx : (x : E) ∈ B) :
    joinSourceCopies hAB jA jB x = jB ⟨x, hx⟩ := by
  classical
  simp only [joinSourceCopies, Function.comp_apply, Equiv.Set.union_apply_right hAB hx,
    Sum.elim_inr]

theorem joinSourceCopies_range {E Y : Type*} {A B : Set E}
    (hAB : Disjoint A B) (jA : A → Y) (jB : B → Y) :
    range (joinSourceCopies hAB jA jB) = range jA ∪ range jB := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rcases x.property with hx | hx
    · exact Or.inl ⟨⟨x, hx⟩, (joinSourceCopies_left hAB jA jB x hx).symm⟩
    · exact Or.inr ⟨⟨x, hx⟩, (joinSourceCopies_right hAB jA jB x hx).symm⟩
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨⟨x, Or.inl x.property⟩, joinSourceCopies_left hAB jA jB _ x.property⟩
    · exact ⟨⟨x, Or.inr x.property⟩, joinSourceCopies_right hAB jA jB _ x.property⟩

theorem joinSourceCopies_injective {E Y : Type*} {A B : Set E}
    (hAB : Disjoint A B) {jA : A → Y} {jB : B → Y}
    (hA : Function.Injective jA) (hB : Function.Injective jB)
    (himages : Disjoint (range jA) (range jB)) :
    Function.Injective (joinSourceCopies hAB jA jB) := by
  intro x y h
  rcases x.property with hx | hx <;> rcases y.property with hy | hy
  · rw [joinSourceCopies_left hAB jA jB x hx, joinSourceCopies_left hAB jA jB y hy] at h
    exact Subtype.ext (congrArg (fun z : A ↦ (z : E)) (hA h))
  · rw [joinSourceCopies_left hAB jA jB x hx, joinSourceCopies_right hAB jA jB y hy] at h
    exact False.elim (disjoint_left.mp himages ⟨⟨x, hx⟩, rfl⟩ ⟨⟨y, hy⟩, h.symm⟩)
  · rw [joinSourceCopies_right hAB jA jB x hx, joinSourceCopies_left hAB jA jB y hy] at h
    exact False.elim (disjoint_left.mp himages ⟨⟨y, hy⟩, h.symm⟩ ⟨⟨x, hx⟩, rfl⟩)
  · rw [joinSourceCopies_right hAB jA jB x hx, joinSourceCopies_right hAB jA jB y hy] at h
    exact Subtype.ext (congrArg (fun z : B ↦ (z : E)) (hB h))

theorem joinSourceCopies_target {E Y X : Type*} {A B : Set E}
    (hAB : Disjoint A B) {jA : A → Y} {jB : B → Y} {f : E → X} {g : Y → X}
    (hA : ∀ x : A, g (jA x) = f x) (hB : ∀ x : B, g (jB x) = f x)
    (x : (A ∪ B : Set E)) : g (joinSourceCopies hAB jA jB x) = f x := by
  rcases x.property with hx | hx
  · rw [joinSourceCopies_left hAB jA jB x hx]
    exact hA ⟨x, hx⟩
  · rw [joinSourceCopies_right hAB jA jB x hx]
    exact hB ⟨x, hx⟩

theorem retained_double_relation_eq
    {E Y X : Type*} {K : Set E} {D N : Set Y} {f : E → X} {g : Y → X}
    (j : K → Y) (hj : Function.Injective j)
    (hcover : range j ∪ N = D) (hkeep : ∀ x : K, g (j x) = f x)
    (hsingle : ∀ z ∈ N, ∀ w ∈ D, g w = g z → w = z) :
    {v : Y × Y | v.1 ∈ D ∧ v.2 ∈ D ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
      (fun v : K × K ↦ (j v.1, j v.2)) ''
        {v : K × K | f v.1 = f v.2 ∧ (v.1 : E) ≠ v.2} := by
  ext v
  constructor
  · rintro ⟨hv0, hv1, heq, hne⟩
    have hn0 : v.1 ∉ N := fun hz ↦ hne (hsingle v.1 hz v.2 hv1 heq.symm).symm
    have hn1 : v.2 ∉ N := fun hz ↦ hne (hsingle v.2 hz v.1 hv0 heq)
    obtain ⟨x, hx⟩ := (hcover.symm.subset hv0).resolve_right hn0
    obtain ⟨y, hy⟩ := (hcover.symm.subset hv1).resolve_right hn1
    refine ⟨(x, y), ⟨?_, ?_⟩, Prod.ext hx hy⟩
    · rw [← hkeep, ← hkeep, hx, hy]
      exact heq
    · intro hxy
      exact hne (hx.symm.trans ((congrArg j (Subtype.ext hxy)).trans hy))
  · rintro ⟨⟨x, y⟩, ⟨heq, hne⟩, rfl⟩
    refine ⟨hcover.subset (Or.inl ⟨x, rfl⟩), hcover.subset (Or.inl ⟨y, rfl⟩), ?_, ?_⟩
    · simpa only [hkeep] using heq
    · intro hxy
      exact hne (congrArg Subtype.val (hj hxy))

theorem retained_double_locus_eq
    {E Y X : Type*} {K : Set E} {D N : Set Y} {f : E → X} {g : Y → X}
    (j : K → Y) (hj : Function.Injective j)
    (hcover : range j ∪ N = D) (hkeep : ∀ x : K, g (j x) = f x)
    (hsingle : ∀ z ∈ N, ∀ w ∈ D, g w = g z → w = z) :
    {z : Y | z ∈ D ∧ ∃ w ∈ D, g z = g w ∧ z ≠ w} =
      j '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y} := by
  have hrel := retained_double_relation_eq j hj hcover hkeep hsingle
  ext z
  constructor
  · rintro ⟨hz, w, hw, heq, hne⟩
    obtain ⟨⟨x, y⟩, hxy, hv⟩ := hrel.subset (show
      (z, w) ∈ {v : Y × Y | v.1 ∈ D ∧ v.2 ∈ D ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2}
      from ⟨hz, hw, heq, hne⟩)
    exact ⟨x, ⟨y, hxy⟩, congrArg Prod.fst hv⟩
  · rintro ⟨x, ⟨y, heq, hne⟩, rfl⟩
    have hxy := hrel.symm.subset ⟨(x, y), ⟨heq, hne⟩, rfl⟩
    exact ⟨hxy.1, j y, hxy.2.1, hxy.2.2⟩

end PoincareConjecture.M76.Dehn
