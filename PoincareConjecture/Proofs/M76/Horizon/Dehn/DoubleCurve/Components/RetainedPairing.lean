import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedPartnerPL

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

def retainedComponentMate {I : Type*} (U : I → Set V2) (K : Set V2)
    (mate : I → I) (hmate : Function.Involutive mate) :
    Equiv.Perm {i // U i ⊆ K ∧ U (mate i) ⊆ K} where
  toFun i := ⟨mate i.val, i.property.2, by simpa only [hmate i.val] using i.property.1⟩
  invFun i := ⟨mate i.val, i.property.2, by simpa only [hmate i.val] using i.property.1⟩
  left_inv i := Subtype.ext (hmate i.val)
  right_inv i := Subtype.ext (hmate i.val)

theorem retainedComponentMate_involutive {I : Type*} (U : I → Set V2) (K : Set V2)
    (mate : I → I) (hmate : Function.Involutive mate) :
    Function.Involutive (retainedComponentMate U K mate hmate) :=
  fun i ↦ Subtype.ext (hmate i.val)

theorem RetainedSquareMapFacts.partner_copy_eq
    {X : Type*} {f g : V2 → X} {K : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j)
    (p : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hvalue : ∀ x : doubleLocusOn f D2, f (p x) = f x)
    (hfree : ∀ x : doubleLocusOn f D2, (p x : V2) ≠ x)
    (q : doubleLocusOn g D2 → doubleLocusOn g D2)
    (hunique : ∀ (x : doubleLocusOn g D2) (y : V2), y ∈ D2 →
      g x = g y → (x : V2) ≠ y → y = (q x : V2))
    (x : doubleLocusOn f D2) (hxK : (x : V2) ∈ K) (hpK : (p x : V2) ∈ K) :
    ∃ hx : j ⟨x, hxK⟩ ∈ doubleLocusOn g D2,
      (q ⟨j ⟨x, hxK⟩, hx⟩ : V2) = j ⟨p x, hpK⟩ := by
  have hval : g (j ⟨x, hxK⟩) = g (j ⟨p x, hpK⟩) := by
    rw [facts.keep, facts.keep]
    exact (hvalue x).symm
  have hne : j ⟨x, hxK⟩ ≠ j ⟨p x, hpK⟩ := by
    intro h
    exact hfree x (congrArg Subtype.val (facts.injective h)).symm
  have hx : j ⟨x, hxK⟩ ∈ doubleLocusOn g D2 :=
    ⟨facts.mapsTo _, _, facts.mapsTo _, hval, hne⟩
  exact ⟨hx, (hunique ⟨_, hx⟩ _ (facts.mapsTo _) hval hne).symm⟩

theorem RetainedSquareMapFacts.partner_mem_component
    {X I : Type*} {f g : V2 → X} {K : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j)
    (U : I → Set V2) (mate : I → I)
    (hcover : ⋃ i, U i = doubleLocusOn f D2)
    (p : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hvalue : ∀ x : doubleLocusOn f D2, f (p x) = f x)
    (hfree : ∀ x : doubleLocusOn f D2, (p x : V2) ≠ x)
    (hmate : ∀ (i : I) (x : doubleLocusOn f D2),
      (x : V2) ∈ U i → (p x : V2) ∈ U (mate i))
    (q : doubleLocusOn g D2 → doubleLocusOn g D2)
    (hunique : ∀ (x : doubleLocusOn g D2) (y : V2), y ∈ D2 →
      g x = g y → (x : V2) ≠ y → y = (q x : V2))
    (i : I) (hpi : U (mate i) ⊆ K)
    (x : doubleLocusOn g D2) (hx : (x : V2) ∈ j '' (Subtype.val ⁻¹' U i)) :
    (q x : V2) ∈ j '' (Subtype.val ⁻¹' U (mate i)) := by
  obtain ⟨a, hai, ha⟩ := hx
  have haG : (a : V2) ∈ doubleLocusOn f D2 := hcover ▸ mem_iUnion.mpr ⟨i, hai⟩
  let aG : doubleLocusOn f D2 := ⟨a, haG⟩
  have hpa : (p aG : V2) ∈ U (mate i) := hmate i aG hai
  obtain ⟨hja, hq⟩ := facts.partner_copy_eq p hvalue hfree q hunique aG a.property (hpi hpa)
  have hax : (⟨j a, hja⟩ : doubleLocusOn g D2) = x := Subtype.ext ha
  rw [hax] at hq
  exact ⟨⟨p aG, hpi hpa⟩, hpa, hq.symm⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
