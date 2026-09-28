import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripHalfDiskComplement

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

def originalStripSheet (i : Bool) (p : P2) : C3 :=
  ((p.2, if i then -p.2 else p.2), p.1)

theorem originalStripSheet_mem_tube (i : Bool) {p : P2} (hp : p ∈ source) :
    originalStripSheet i p ∈ tube := by
  cases i
  · exact ⟨⟨hp.2, hp.2⟩, hp.1⟩
  · refine ⟨⟨hp.2, ?_⟩, hp.1⟩
    change -1 ≤ -p.2 ∧ -p.2 ≤ 1
    constructor <;> linarith [hp.2.1, hp.2.2]

theorem originalStripSheet_eq_iff (i j : Bool) (p q : P2) :
    originalStripSheet i p = originalStripSheet j q ↔ p = q ∧ (i = j ∨ p.2 = 0) := by
  constructor
  · intro h
    have hpq : p = q := congrArg (fun z : C3 ↦ (z.2, z.1.1)) h
    refine ⟨hpq, ?_⟩
    subst q
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      have hu := congrArg (fun z : C3 ↦ z.1.2) h
      cases i <;> cases j
      · exact False.elim (hij rfl)
      · change p.2 = -p.2 at hu
        linarith
      · change -p.2 = p.2 at hu
        linarith
      · exact False.elim (hij rfl)
  · rintro ⟨rfl, hij | hp⟩
    · rw [hij]
    · cases i <;> cases j <;> simp [originalStripSheet, hp]

theorem original_strip_distinct_mate_iff
    {E X : Type*} {S : Set E} (c : Bool → P2 → E) {f : E → X} {τ : C3 → X}
    (hdisj : Disjoint (c false '' source) (c true '' source)) (hτ : InjOn τ tube)
    (hfull : S ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (i : Bool) (p : source) {x : E} (hx : x ∈ S) :
    (x ≠ c i p ∧ f x = f (c i p)) ↔ p.val.2 = 0 ∧ x = c (!i) (p.val.1, 0) := by
  have hsheet (j : Bool) (q : P2) (hq : q ∈ source) :
      f (c j q) = τ (originalStripSheet j q) := by
    cases j
    · exact h0 q hq
    · exact h1 q hq
  have hcross (j : Bool) {p q : P2} (hp : p ∈ source) (hq : q ∈ source) :
      c (!j) q ≠ c j p := by
    cases j
    · intro h
      exact disjoint_left.mp hdisj ⟨p, hp, rfl⟩ ⟨q, hq, h⟩
    · intro h
      exact disjoint_left.mp hdisj ⟨q, hq, h⟩ ⟨p, hp, rfl⟩
  constructor
  · rintro ⟨hne, heq⟩
    have hxTube : x ∈ S ∩ f ⁻¹' (τ '' tube) :=
      ⟨hx, ⟨originalStripSheet i p, originalStripSheet_mem_tube i p.property,
        ((hsheet i p p.property).symm.trans heq.symm)⟩⟩
    have hxStrip : ∃ j q, q ∈ source ∧ c j q = x := by
      rcases hfull.subset hxTube with ⟨q, hq, hqx⟩ | ⟨q, hq, hqx⟩
      · exact ⟨false, q, hq, hqx⟩
      · exact ⟨true, q, hq, hqx⟩
    obtain ⟨j, q, hq, rfl⟩ := hxStrip
    have hcoord := hτ (originalStripSheet_mem_tube j hq)
      (originalStripSheet_mem_tube i p.property)
      ((hsheet j q hq).symm.trans (heq.trans (hsheet i p p.property)))
    obtain ⟨hqp, hji | hzero⟩ := (originalStripSheet_eq_iff j i q p).mp hcoord
    · exact False.elim (hne (by rw [hji, hqp]))
    · have hji : j ≠ i := by
        intro hji
        exact hne (by rw [hji, hqp])
      have hj : j = !i := by cases i <;> cases j <;> simp_all
      have hp0 : p.val.2 = 0 := (congrArg Prod.snd hqp).symm.trans hzero
      refine ⟨hp0, ?_⟩
      rw [hj, hqp]
      exact congrArg (c (!i)) (Prod.ext rfl hp0)
  · rintro ⟨hp0, rfl⟩
    have hcenter : (p.val.1, (0 : ℝ)) ∈ source := ⟨p.property.1, by norm_num⟩
    refine ⟨hcross i p.property hcenter, ?_⟩
    rw [hsheet (!i) _ hcenter, hsheet i p p.property]
    apply congrArg τ
    apply (originalStripSheet_eq_iff (!i) i (p.val.1, 0) p).mpr
    exact ⟨Prod.ext rfl hp0.symm, Or.inr rfl⟩

theorem original_strip_has_mate_iff
    {E X : Type*} {S : Set E} (c : Bool → P2 → E) {f : E → X} {τ : C3 → X}
    (hcS : ∀ i, MapsTo (c i) source S)
    (hdisj : Disjoint (c false '' source) (c true '' source)) (hτ : InjOn τ tube)
    (hfull : S ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (i : Bool) (p : source) :
    (∃ x ∈ S, x ≠ c i p ∧ f x = f (c i p)) ↔ p.val.2 = 0 := by
  constructor
  · rintro ⟨x, hx, hmate⟩
    exact ((original_strip_distinct_mate_iff c hdisj hτ hfull h0 h1 i p hx).mp hmate).1
  · intro hp0
    have hcenter : (p.val.1, (0 : ℝ)) ∈ source := ⟨p.property.1, by norm_num⟩
    refine ⟨c (!i) (p.val.1, 0), hcS (!i) hcenter, ?_⟩
    exact (original_strip_distinct_mate_iff c hdisj hτ hfull h0 h1 i p
      (hcS (!i) hcenter)).mpr ⟨hp0, rfl⟩

theorem original_strip_center_unique_mate
    {E X : Type*} {S : Set E} (c : Bool → P2 → E) {f : E → X} {τ : C3 → X}
    (hcS : ∀ i, MapsTo (c i) source S)
    (hdisj : Disjoint (c false '' source) (c true '' source)) (hτ : InjOn τ tube)
    (hfull : S ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (i : Bool) (t : Icc (0 : ℝ) 1) :
    ∃! x : E, x ∈ S ∧ x ≠ c i (t, 0) ∧ f x = f (c i (t, 0)) := by
  let p : source := ⟨(t, 0), t.property, by norm_num⟩
  have hmate (x : E) (hx : x ∈ S) :=
    original_strip_distinct_mate_iff c hdisj hτ hfull h0 h1 i p hx
  have hcenter : c (!i) (t, 0) ∈ S := hcS (!i) p.property
  refine ⟨c (!i) (t, 0), ⟨hcenter, (hmate _ hcenter).mpr ⟨rfl, rfl⟩⟩, ?_⟩
  intro x hx
  exact ((hmate x hx.1).mp hx.2).2

theorem original_double_locus_inter_strips
    {E X : Type*} {S : Set E} (c : Bool → P2 → E) {f : E → X} {τ : C3 → X}
    (hcS : ∀ i, MapsTo (c i) source S)
    (hdisj : Disjoint (c false '' source) (c true '' source)) (hτ : InjOn τ tube)
    (hfull : S ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1)) :
    {x : E | x ∈ S ∧ ∃ y ∈ S, f x = f y ∧ x ≠ y} ∩
      ((c false '' source) ∪ (c true '' source)) =
        (c false '' arm 0) ∪ (c true '' arm 0) := by
  have hpoint (i : Bool) (p : P2) (hp : p ∈ source) :
      (c i p ∈ S ∧ ∃ y ∈ S, f (c i p) = f y ∧ c i p ≠ y) ↔ p.2 = 0 := by
    constructor
    · rintro ⟨_, y, hy, heq, hne⟩
      exact (original_strip_has_mate_iff c hcS hdisj hτ hfull h0 h1 i ⟨p, hp⟩).mp
        ⟨y, hy, Ne.symm hne, heq.symm⟩
    · intro hp0
      obtain ⟨y, hy, hne, heq⟩ :=
        (original_strip_has_mate_iff c hcS hdisj hτ hfull h0 h1 i ⟨p, hp⟩).mpr hp0
      exact ⟨hcS i hp, y, hy, heq.symm, Ne.symm hne⟩
  have hcenter : arm 0 ⊆ source :=
    (arm_zero_subset_halfSource false).trans (halfSource_subset_source false)
  ext x
  constructor
  · rintro ⟨hx, ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩⟩
    · exact Or.inl ⟨p, ⟨hp.1, (hpoint false p hp).mp hx⟩, rfl⟩
    · exact Or.inr ⟨p, ⟨hp.1, (hpoint true p hp).mp hx⟩, rfl⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨(hpoint false p (hcenter hp)).mpr hp.2, Or.inl ⟨p, hcenter hp, rfl⟩⟩
    · exact ⟨(hpoint true p (hcenter hp)).mpr hp.2, Or.inr ⟨p, hcenter hp, rfl⟩⟩

theorem old_double_subset_avoids_strips
    {E X : Type*} {S K : Set E} (c : Bool → P2 → E) {f : E → X} {τ : C3 → X}
    (hcS : ∀ i, MapsTo (c i) source S)
    (hdisj : Disjoint (c false '' source) (c true '' source)) (hτ : InjOn τ tube)
    (hfull : S ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hK : K ⊆ {x : E | x ∈ S ∧ ∃ y ∈ S, f x = f y ∧ x ≠ y})
    (hcenters : Disjoint K ((c false '' arm 0) ∪ (c true '' arm 0))) :
    Disjoint K ((c false '' source) ∪ (c true '' source)) := by
  apply disjoint_left.mpr
  intro x hx hxstrips
  exact disjoint_left.mp hcenters hx
    ((original_double_locus_inter_strips c hcS hdisj hτ hfull h0 h1).subset
      ⟨hK hx, hxstrips⟩)

theorem strip_center_disjoint_of_far_contact
    {E : Type*} (c : P2 → E) (hci : InjOn c source) (positive : Bool)
    {A : Set E} (hcontact : A ∩ c '' source = c '' arm (farArmParameter positive)) :
    Disjoint (c '' arm 0) A := by
  have hcenter : arm 0 ⊆ source :=
    (arm_zero_subset_halfSource false).trans (halfSource_subset_source false)
  apply disjoint_left.mpr
  intro x hx hxA
  exact disjoint_left.mp (disjoint_center_far_images c hci positive) hx
    (hcontact.subset ⟨hxA, image_mono hcenter hx⟩)

theorem strip_center_disjoint_of_no_contact
    {E : Type*} (c : P2 → E) {A : Set E} (hcontact : A ∩ c '' source = ∅) :
    Disjoint (c '' arm 0) A := by
  have hcenter : arm 0 ⊆ source :=
    (arm_zero_subset_halfSource false).trans (halfSource_subset_source false)
  apply disjoint_left.mpr
  intro x hx hxA
  exact Set.notMem_empty x (hcontact.subset ⟨hxA, image_mono hcenter hx⟩)

theorem original_strip_centers_disjoint_exteriors
    {E : Type*} (c : Bool → P2 → E) (hci : ∀ i, InjOn (c i) source)
    {A M C : Set E} (s0 s1 : Bool)
    (hA0 : A ∩ c false '' source = c false '' arm (farArmParameter (!s0)))
    (hA1 : A ∩ c true '' source = ∅)
    (hM0 : M ∩ c false '' source = c false '' arm (farArmParameter s0))
    (hM1 : M ∩ c true '' source = c true '' arm (farArmParameter s1))
    (hC0 : C ∩ c false '' source = ∅)
    (hC1 : C ∩ c true '' source = c true '' arm (farArmParameter (!s1))) :
    Disjoint (c false '' arm 0) ((A ∪ M) ∪ C) ∧
      Disjoint (c true '' arm 0) ((A ∪ M) ∪ C) := by
  constructor
  · exact disjoint_union_right.mpr ⟨disjoint_union_right.mpr
      ⟨strip_center_disjoint_of_far_contact (c false) (hci false) (!s0) hA0,
        strip_center_disjoint_of_far_contact (c false) (hci false) s0 hM0⟩,
      strip_center_disjoint_of_no_contact (c false) hC0⟩
  · exact disjoint_union_right.mpr ⟨disjoint_union_right.mpr
      ⟨strip_center_disjoint_of_no_contact (c true) hA1,
        strip_center_disjoint_of_far_contact (c true) (hci true) s1 hM1⟩,
      strip_center_disjoint_of_far_contact (c true) (hci true) (!s1) hC1⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
