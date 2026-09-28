import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberInterpolation



set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_prism_reflection_of_interpolation
    {E ι : Type*} [TopologicalSpace E] {A B : ι → Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i,B i) × I,(⋃ i,B i)))
    (hL : ∀ i (y : B i) t, (L (⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) y t) :
    ∃ J : (⋃ i,B i) ≃ₜ (⋃ i,B i), Function.Involutive J ∧
      (∀ i (y : B i), (J ⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩ : E) =
        prismFiberReflection (H i) y) ∧
      (∀ i (y : B i),
        (((H i).symm y : E × ℝ).2 = 0 ∨ ((H i).symm y : E × ℝ).2 = 1) →
        (J ⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩ : E) ≠ y) := by
  let f : (⋃ i,B i) → (⋃ i,B i) := fun x => L (x,1)
  have hf (i) (y : B i) : (f ⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩ : E) =
      prismFiberReflection (H i) y := by
    dsimp only [f]
    rw [hL]
    apply congrArg (fun z : B i => (z : E))
    unfold prismFiberInterpolation
    rw [fiberInterpolation_one]
    rfl
  have hinv : Function.Involutive f := by
    intro x
    obtain ⟨i,hi⟩ := mem_iUnion.mp x.property
    have he : f x = ⟨prismFiberReflection (H i) ⟨x,hi⟩,
        mem_iUnion.mpr ⟨i,(prismFiberReflection (H i) ⟨x,hi⟩).property⟩⟩ :=
      Subtype.ext (hf i ⟨x,hi⟩)
    apply Subtype.ext
    rw [he,hf,prismFiberReflection_involutive]
  have hfc : Continuous f := by unfold f; fun_prop
  let J : (⋃ i,B i) ≃ₜ (⋃ i,B i) :=
    { toEquiv := ⟨f,f,hinv,hinv⟩, continuous_toFun := hfc, continuous_invFun := hfc }
  refine ⟨J,hinv,hf,?_⟩
  intro i y hy he
  have heq : prismFiberReflection (H i) y = y := Subtype.ext ((hf i y).symm.trans he)
  have hh := (prismFiberReflection_eq_iff_height (H i) y).mp heq
  rcases hy with hy | hy <;> linarith

end PoincareConjecture.M76.PrismBelt
