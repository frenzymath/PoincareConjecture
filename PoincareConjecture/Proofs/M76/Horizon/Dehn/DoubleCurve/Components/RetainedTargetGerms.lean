import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalResolutionProperness

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem RetainedSquareMapFacts.old_fiber_subset
    {X : Type*} {f g : V2 → X} {K : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2))
    {x y : V2} (hx : x ∈ D2) (hy : y ∈ D2) (hxy : g x = g y) (hne : x ≠ y) :
    D2 ∩ f ⁻¹' {g x} ⊆ K := by
  have hrel : (x, y) ∈
      {v : V2 × V2 | v.1 ∈ D2 ∧ v.2 ∈ D2 ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} :=
    ⟨hx, hy, hxy, hne⟩
  rw [facts.double_relation] at hrel
  obtain ⟨⟨a, b⟩, ⟨hab, hneab⟩, hjab⟩ := hrel
  have hja : j a = x := congrArg Prod.fst hjab
  have hfa : f a = g x := (facts.keep a).symm.trans (congrArg g hja)
  let aG : doubleLocusOn f D2 := ⟨a, facts.old_subset a.property, b,
    facts.old_subset b.property, hab, hneab⟩
  intro z hz
  have hfz : f z = g x := hz.2
  by_cases hza : z = (a : V2)
  · exact hza ▸ a.property
  · have hzb : z = (b : V2) :=
      (hunique aG z hz.1 (hfa.trans hfz.symm) (Ne.symm hza)).trans
        (hunique aG b (facts.old_subset b.property) hab hneab).symm
    exact hzb ▸ b.property

theorem RetainedSquareMapFacts.double_target_avoids
    {X : Type*} {f g : V2 → X} {K B : Set V2} {T : Set X} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j)
    (hbad : doubleLocusOn f D2 ∩ f ⁻¹' T ⊆ B) (hKB : Disjoint K B)
    {x y : V2} (hx : x ∈ D2) (hy : y ∈ D2) (hxy : g x = g y) (hne : x ≠ y) :
    g x ∉ T := by
  intro hxT
  have hrel : (x, y) ∈
      {v : V2 × V2 | v.1 ∈ D2 ∧ v.2 ∈ D2 ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} :=
    ⟨hx, hy, hxy, hne⟩
  rw [facts.double_relation] at hrel
  obtain ⟨⟨a, b⟩, ⟨hab, hneab⟩, hjab⟩ := hrel
  have hja : j a = x := congrArg Prod.fst hjab
  have haG : (a : V2) ∈ doubleLocusOn f D2 :=
    ⟨facts.old_subset a.property, b, facts.old_subset b.property, hab, hneab⟩
  have haT : f a ∈ T := by
    rw [← facts.keep a, hja]
    exact hxT
  exact disjoint_left.mp hKB a.property (hbad ⟨haG, haT⟩)

theorem RetainedSquareMapFacts.image_inter_eq
    {X : Type*} {f g : V2 → X} {K B : Set V2} {T W : Set X} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j)
    (hcover : D2 ⊆ K ∪ B) (himage : g '' D2 ⊆ f '' D2 ∪ T)
    (hW : Disjoint W (f '' B ∪ T)) :
    g '' D2 ∩ W = f '' D2 ∩ W := by
  ext z
  constructor
  · rintro ⟨hz, hzW⟩
    rcases himage hz with hz | hz
    · exact ⟨hz, hzW⟩
    · exact False.elim (disjoint_left.mp hW hzW (Or.inr hz))
  · rintro ⟨⟨x, hx, rfl⟩, hxW⟩
    rcases hcover hx with hxK | hxB
    · exact ⟨⟨j ⟨x, hxK⟩, facts.mapsTo _, facts.keep _⟩, hxW⟩
    · exact False.elim (disjoint_left.mp hW hxW (Or.inl ⟨x, hxB, rfl⟩))

theorem RetainedSquareMapFacts.exists_image_germ
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {f g : V2 → X} {K B : Set V2} {T : Set X} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2))
    (hBS : B ⊆ D2) (hKB : Disjoint K B)
    (hcover : D2 ⊆ K ∪ B) (himage : g '' D2 ⊆ f '' D2 ∪ T)
    (hB : IsCompact (f '' B)) (hT : IsCompact T)
    {x y : V2} (hx : x ∈ D2) (hy : y ∈ D2) (hxy : g x = g y) (hne : x ≠ y)
    (hxT : g x ∉ T) :
    ∃ W : Set X, IsOpen W ∧ g x ∈ W ∧ g '' D2 ∩ W = f '' D2 ∩ W := by
  have hxB : g x ∉ f '' B := by
    rintro ⟨z, hz, hzval⟩
    exact disjoint_left.mp hKB
      (facts.old_fiber_subset partner hunique hx hy hxy hne ⟨hBS hz, hzval⟩) hz
  refine ⟨(f '' B ∪ T)ᶜ, (hB.union hT).isClosed.isOpen_compl, ?_, ?_⟩
  · exact fun h ↦ h.elim hxB hxT
  · exact facts.image_inter_eq hcover himage disjoint_compl_left

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
