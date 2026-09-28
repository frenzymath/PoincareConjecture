import Mathlib.Topology.ContinuousMap.Basic








set_option autoImplicit false

open scoped Topology

namespace Topology.IsQuotientMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] {f : C(X, Y)} {g : C(X, Z)}


noncomputable def homeomorphOfFibers (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (h : ∀ x x', f x = f x' ↔ g x = g x') : Y ≃ₜ Z where
  toFun := hf.lift g (fun {x x'} hx ↦ (h x x').mp hx)
  invFun := hg.lift f (fun {x x'} hx ↦ (h x x').mpr hx)
  left_inv := by
    intro y
    obtain ⟨x, rfl⟩ := hf.surjective y
    have hfg := congrArg (fun k : C(X, Z) ↦ k x) (hf.lift_comp g (fun {x x'} hx ↦ (h x x').mp hx))
    have hgf := congrArg (fun k : C(X, Y) ↦ k x) (hg.lift_comp f (fun {x x'} hx ↦ (h x x').mpr hx))
    change (hg.lift f _) ((hf.lift g _) (f x)) = f x
    simp only [ContinuousMap.comp_apply] at hfg hgf
    rw [hfg]
    exact hgf
  right_inv := by
    intro z
    obtain ⟨x, rfl⟩ := hg.surjective z
    have hfg := congrArg (fun k : C(X, Z) ↦ k x) (hf.lift_comp g (fun {x x'} hx ↦ (h x x').mp hx))
    have hgf := congrArg (fun k : C(X, Y) ↦ k x) (hg.lift_comp f (fun {x x'} hx ↦ (h x x').mpr hx))
    change (hf.lift g _) ((hg.lift f _) (g x)) = g x
    simp only [ContinuousMap.comp_apply] at hfg hgf
    rw [hgf]
    exact hfg
  continuous_toFun := (hf.lift g _).continuous
  continuous_invFun := (hg.lift f _).continuous

@[simp]
theorem homeomorphOfFibers_apply (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (h : ∀ x x', f x = f x' ↔ g x = g x') (x : X) :
    hf.homeomorphOfFibers hg h (f x) = g x :=
  congrArg (fun k : C(X, Z) ↦ k x)
    (hf.lift_comp g (fun {x x'} hx ↦ (h x x').mp hx))

end Topology.IsQuotientMap

namespace IsOpenQuotientMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}


theorem restrictPreimage_of_isOpen_preimage (hf : IsOpenQuotientMap f) (s : Set Y)
    (hs : IsOpen (f ⁻¹' s)) : IsOpenQuotientMap (s.restrictPreimage f) :=
  ⟨hf.surjective.restrictPreimage s, hf.continuous.restrictPreimage,
    hf.isOpenMap.mapsToRestrict hs (Set.mapsTo_preimage f s)⟩

end IsOpenQuotientMap

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]


theorem isOpenQuotientMap_of_pair_fibers (r : Setoid X) (τ : X → X)
    (hτ : Continuous τ) (hr : ∀ x y, r x y ↔ x = y ∨ x = τ y) :
    IsOpenQuotientMap (@Quotient.mk' X r) := by
  refine ⟨Quotient.mk'_surjective, continuous_quotient_mk', ?_⟩
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  have hsat : (@Quotient.mk' X r) ⁻¹' ((@Quotient.mk' X r) '' U) =
      U ∪ τ ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      rcases (hr y x).mp (Quotient.exact heq) with h | h
      · exact Or.inl (h ▸ hy)
      · exact Or.inr (show τ x ∈ U from h ▸ hy)
    · rintro (hx | hx)
      · exact ⟨x, hx, rfl⟩
      · exact ⟨τ x, hx, Quotient.sound ((hr (τ x) x).mpr (Or.inr rfl))⟩
  rw [hsat]
  exact hU.union (hU.preimage hτ)

end Poincare.Topology
