import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalCrossingResolution

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1

def minusArmPoint (t : I01) : source := ⟨(t, -1), t.property, by norm_num⟩

def plusArmPoint (t : I01) : source := ⟨(t, 1), t.property, by norm_num⟩

theorem minusArmPoint_injective : Function.Injective minusArmPoint := by
  intro s t h
  exact Subtype.ext (congrArg (fun x : source ↦ x.val.1) h)

theorem plusArmPoint_injective : Function.Injective plusArmPoint := by
  intro s t h
  exact Subtype.ext (congrArg (fun x : source ↦ x.val.1) h)

theorem retained_tube_preimage
    {E X : Type*} {S A B0 B1 W0 W1 : Set E} {f : E → X} {U : Set X}
    (hfull : S ∩ f ⁻¹' U = B0 ∪ B1) (hAS : A ⊆ S)
    (h0 : A ∩ B0 = W0) (h1 : A ∩ B1 = W1) :
    A ∩ f ⁻¹' U = W0 ∪ W1 := by
  calc
    A ∩ f ⁻¹' U = A ∩ (S ∩ f ⁻¹' U) := by rw [← inter_assoc, inter_eq_left.mpr hAS]
    _ = A ∩ (B0 ∪ B1) := by rw [hfull]
    _ = W0 ∪ W1 := by rw [inter_union_distrib_left, h0, h1]

theorem replacement_target_injective {X : Type*} {τ : C3 → X}
    (hτ : InjOn τ tube) {b : ℝ} (hb : b ≤ 1) (positive : Bool) :
    Function.Injective (fun p : source ↦ τ (strip b positive p)) ∧
      Function.Injective (fun p : source ↦ τ (alternate b positive p)) := by
  constructor
  · intro p q h
    exact Subtype.ext ((embedding_maps b positive).1.injective
      (hτ ((mapsTo_tube hb positive).1 p.property)
        ((mapsTo_tube hb positive).1 q.property) h))
  · intro p q h
    exact Subtype.ext ((embedding_maps b positive).2.injective
      (hτ ((mapsTo_tube hb positive).2 p.property)
        ((mapsTo_tube hb positive).2 q.property) h))

theorem alternate_target_disjoint {X : Type*} {τ : C3 → X}
    (hτ : InjOn τ tube) {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) :
    Disjoint (range (fun p : source ↦ τ (alternate b false p)))
      (range (fun p : source ↦ τ (alternate b true p))) := by
  apply disjoint_left.mpr
  rintro z ⟨p, rfl⟩ ⟨q, hq⟩
  have heq := hτ ((mapsTo_tube hb1 true).2 q.property)
    ((mapsTo_tube hb1 false).2 p.property) hq
  exact disjoint_left.mp (separated_pairs hb0).2.2 ⟨q, rfl⟩ ⟨p, heq.symm⟩

theorem retained_replacement_fiber
    {E X Y : Type*} {A : Set E} {f : E → X} {τ : C3 → X}
    {r : Y → C3} {p : I01 → E} {arm : I01 → Y}
    (hpre : A ∩ f ⁻¹' (τ '' tube) = range p)
    (hr : ∀ y, r y ∈ tube) (hinj : Function.Injective (τ ∘ r))
    (harm : Function.Injective arm) (hp : ∀ t, f (p t) = τ (r (arm t)))
    (x : A) (y : Y) : f x = τ (r y) ↔
    ∃! t : I01, (x : E) = p t ∧ y = arm t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := hpre.subset ⟨x.property, ⟨r y, hr y, h.symm⟩⟩
    have hy : arm t = y := hinj ((hp t).symm.trans ((congrArg f ht).trans h))
    exact ⟨t, ⟨ht.symm, hy.symm⟩, fun u hu ↦ harm (hu.2.symm.trans hy.symm)⟩
  · rintro ⟨t, ht, _⟩
    rw [ht.1, ht.2, hp]

theorem retained_replacement_ne
    {E X Y : Type*} {A : Set E} {f : E → X} {τ : C3 → X} {r : Y → C3}
    (hpre : A ∩ f ⁻¹' (τ '' tube) = ∅) (hr : ∀ y, r y ∈ tube)
    (x : A) (y : Y) : f x ≠ τ (r y) := by
  intro h
  exact Set.notMem_empty _ (hpre.subset ⟨x.property, ⟨r y, hr y, h.symm⟩⟩)

theorem retained_two_replacement_fiber
    {E X Y Y' : Type*} {A : Set E} {f : E → X} {τ : C3 → X}
    {r : Y → C3} {r' : Y' → C3} {p q : I01 → E}
    {arm : I01 → Y} {arm' : I01 → Y'}
    (hpre : A ∩ f ⁻¹' (τ '' tube) = range p ∪ range q)
    (hr : ∀ y, r y ∈ tube) (hinj : Function.Injective (τ ∘ r))
    (harm : Function.Injective arm) (hp : ∀ t, f (p t) = τ (r (arm t)))
    (hq : ∀ t, f (q t) = τ (r' (arm' t)))
    (hdisj : Disjoint (range (τ ∘ r)) (range (τ ∘ r')))
    (x : A) (y : Y) : f x = τ (r y) ↔
    ∃! t : I01, (x : E) = p t ∧ y = arm t := by
  constructor
  · intro h
    rcases hpre.subset ⟨x.property, ⟨r y, hr y, h.symm⟩⟩ with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hy : arm t = y := hinj ((hp t).symm.trans ((congrArg f ht).trans h))
      exact ⟨t, ⟨ht.symm, hy.symm⟩, fun u hu ↦ harm (hu.2.symm.trans hy.symm)⟩
    · exact False.elim (disjoint_left.mp hdisj ⟨y, rfl⟩
        ⟨arm' t, (hq t).symm.trans ((congrArg f ht).trans h)⟩)
  · rintro ⟨t, ht, _⟩
    rw [ht.1, ht.2, hp]

theorem retained_opposite_replacement_ne
    {E X Y Y' : Type*} {A : Set E} {f : E → X} {τ : C3 → X}
    {r : Y → C3} {r' : Y' → C3} {q : I01 → E} {arm' : I01 → Y'}
    (hpre : A ∩ f ⁻¹' (τ '' tube) = range q) (hr : ∀ y, r y ∈ tube)
    (hq : ∀ t, f (q t) = τ (r' (arm' t)))
    (hdisj : Disjoint (range (τ ∘ r)) (range (τ ∘ r')))
    (x : A) (y : Y) : f x ≠ τ (r y) := by
  intro h
  obtain ⟨t, ht⟩ := hpre.subset ⟨x.property, ⟨r y, hr y, h.symm⟩⟩
  exact disjoint_left.mp hdisj ⟨y, rfl⟩
    ⟨arm' t, (hq t).symm.trans ((congrArg f ht).trans h)⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
