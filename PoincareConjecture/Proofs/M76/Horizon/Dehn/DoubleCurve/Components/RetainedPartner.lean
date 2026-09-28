import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedModels
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalResolutionProperness









set_option autoImplicit false

open Set Metric Topology

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1



theorem RetainedSquareMapFacts.exists_double_locus_copy
    {X : Type*} {f g : V2 → X} {K : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j) (hK : IsCompact K) :
    ∃ H : doubleLocusOn f K ≃ₜ doubleLocusOn g D2,
      ∀ x, (H x : V2) = j ⟨x, x.property.1⟩ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLK : doubleLocusOn f K ⊆ K := fun _ hx ↦ hx.1
  let J : doubleLocusOn f K → V2 := j ∘ Set.inclusion hLK
  have hJ : IsEmbedding J :=
    (facts.continuous.isClosedEmbedding facts.injective).isEmbedding.comp
      (IsEmbedding.inclusion hLK)
  have hrange : range J = doubleLocusOn g D2 := by
    rw [show doubleLocusOn g D2 = _ from facts.double_locus]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy, heq, hne⟩ := x.property.2
      exact ⟨⟨x, x.property.1⟩, ⟨⟨y, hy⟩, heq, hne⟩, rfl⟩
    · rintro ⟨x, ⟨y, heq, hne⟩, rfl⟩
      exact ⟨⟨x, x.property, y, y.property, heq, hne⟩, rfl⟩
  exact ⟨hJ.toHomeomorph.trans (Homeomorph.setCongr hrange), fun _ ↦ rfl⟩




theorem exists_restricted_double_partner
    {X : Type*} {f : V2 → X} {K : Set V2} (hKS : K ⊆ D2)
    (p : doubleLocusOn f D2 ≃ₜ doubleLocusOn f D2)
    (hp : Function.Involutive p)
    (hvalue : ∀ x, f (p x) = f x)
    (hfree : ∀ x, (p x : V2) ≠ x)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (p x : V2)) :
    ∃ q : doubleLocusOn f K ≃ₜ doubleLocusOn f K,
      Function.Involutive q ∧
      ∀ x : doubleLocusOn f K,
        ∃ hx : (x : V2) ∈ doubleLocusOn f D2, (q x : V2) = p ⟨x, hx⟩ := by
  have hsub : doubleLocusOn f K ⊆ doubleLocusOn f D2 := by
    rintro x ⟨hx, y, hy, hxy, hne⟩
    exact ⟨hKS hx, y, hKS hy, hxy, hne⟩
  let inc := Set.inclusion hsub
  have hmem (x : doubleLocusOn f K) : (p (inc x) : V2) ∈ doubleLocusOn f K := by
    obtain ⟨y, hy, hxy, hne⟩ := x.property.2
    have hyval := hunique (inc x) y (hKS hy) hxy hne
    exact ⟨hyval ▸ hy, x, x.property.1, hvalue (inc x), hfree (inc x)⟩
  let q (x : doubleLocusOn f K) : doubleLocusOn f K := ⟨p (inc x), hmem x⟩
  have hinc (x : doubleLocusOn f K) : inc (q x) = p (inc x) := rfl
  have hq : Function.Involutive q := by
    intro x
    apply Subtype.ext
    change (p (inc (q x)) : V2) = x
    rw [hinc, hp]
  have hqc : Continuous q :=
    ((p.continuous.comp (continuous_inclusion hsub)).subtype_val).subtype_mk hmem
  let Q : doubleLocusOn f K ≃ₜ doubleLocusOn f K :=
    ⟨⟨q, q, hq, hq⟩, hqc, hqc⟩
  exact ⟨Q, hq, fun x ↦ ⟨hsub x.property, rfl⟩⟩



theorem RetainedSquareMapFacts.exists_partner
    {X : Type*} {f g : V2 → X} {K : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j) (hK : IsCompact K)
    (p : doubleLocusOn f D2 ≃ₜ doubleLocusOn f D2)
    (hp : Function.Involutive p)
    (hvalue : ∀ x, f (p x) = f x)
    (hfree : ∀ x, (p x : V2) ≠ x)
    (hrim : ∀ x, (p x : V2) ∈ Q2 ↔ (x : V2) ∈ Q2)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (p x : V2)) :
    ∃ q : doubleLocusOn g D2 ≃ₜ doubleLocusOn g D2,
      Function.Involutive q ∧
      (∀ x, g (q x) = g x) ∧ (∀ x, (q x : V2) ≠ x) ∧
      (∀ x, (q x : V2) ∈ Q2 ↔ (x : V2) ∈ Q2) ∧
      (∀ (x : doubleLocusOn g D2) (y : V2), y ∈ D2 →
        g x = g y → (x : V2) ≠ y → y = (q x : V2)) := by
  obtain ⟨H, hH⟩ := facts.exists_double_locus_copy hK
  obtain ⟨r, hr, hrval⟩ := exists_restricted_double_partner facts.old_subset p hp hvalue hfree hunique
  let q := H.symm.trans (r.trans H)
  have hqval (x : doubleLocusOn f K) : q (H x) = H (r x) := by simp [q]
  have hq2 : Function.Involutive q := by
    intro x
    obtain ⟨a, rfl⟩ := H.surjective x
    rw [hqval, hqval, hr]
  have hkeep (x : doubleLocusOn f K) : g (H x) = f x := by
    rw [hH]
    exact facts.keep _
  have hqvalue : ∀ x, g (q x) = g x := by
    intro x
    obtain ⟨a, rfl⟩ := H.surjective x
    rw [hqval, hkeep, hkeep]
    obtain ⟨ha, hval⟩ := hrval a
    rw [hval]
    exact hvalue ⟨a, ha⟩
  have hqfree : ∀ x, (q x : V2) ≠ x := by
    intro x h
    obtain ⟨a, rfl⟩ := H.surjective x
    rw [hqval] at h
    have hra : r a = a := H.injective (Subtype.ext h)
    obtain ⟨ha, hval⟩ := hrval a
    exact hfree ⟨a, ha⟩ (hval.symm.trans (congrArg Subtype.val hra))
  refine ⟨q, hq2, hqvalue, hqfree, ?_, ?_⟩
  · intro x
    obtain ⟨a, rfl⟩ := H.surjective x
    rw [hqval, hH, hH, facts.boundary, facts.boundary]
    obtain ⟨ha, hval⟩ := hrval a
    rw [hval]
    exact hrim ⟨a, ha⟩
  · intro x y hy hxy hne
    have hold : ∀ a ∈ D2, ∀ b ∈ D2, ∀ d ∈ D2,
        f a = f b → f a = f d → a ≠ b → a ≠ d → b = d := by
      intro a ha b hb d hd hab had hnab hnad
      let aG : doubleLocusOn f D2 := ⟨a, ha, b, hb, hab, hnab⟩
      exact (hunique aG b hb hab hnab).trans (hunique aG d hd had hnad).symm
    exact facts.unique_other_point hold x x.property.1 y hy (q x) (q x).property.1
      hxy (hqvalue x).symm hne (Ne.symm (hqfree x))

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
