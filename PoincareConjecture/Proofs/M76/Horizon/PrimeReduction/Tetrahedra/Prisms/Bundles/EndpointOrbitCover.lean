import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberReflection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.FreeInvolutionQuotient









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

def prismEndMap {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : A) (b : Bool) : B :=
  H ⟨((x : E),if b then (1 : ℝ) else 0),x.property,by cases b <;> norm_num⟩

def prismEnds {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) : Set E :=
  range (fun z : A × Bool => (prismEndMap H z.1 z.2 : E))

theorem prismEnds_subset {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) : prismEnds H ⊆ B := by
  rintro _ ⟨z,rfl⟩
  exact (prismEndMap H z.1 z.2).property

theorem prismFiberReflection_end {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : A) (b : Bool) :
    prismFiberReflection H (prismEndMap H x b) = prismEndMap H x (!b) := by
  apply H.symm.injective
  simp only [prismFiberReflection,prismEndMap,Homeomorph.trans_apply,
    H.symm_apply_apply]
  apply Subtype.ext
  rw [productFiberReflection_value]
  cases b <;> simp

theorem prismEndMap_flip_ne {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : A) (b : Bool) :
    prismEndMap H x (!b) ≠ prismEndMap H x b := by
  intro h
  have ht := congrArg (fun z : (A ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).2)
    (H.injective h)
  cases b <;> norm_num [prismEndMap] at ht

theorem exists_prism_endpoint_orbit_cover
    {E ι : Type*} [TopologicalSpace E] [T2Space E]
    (A B : ι → Set E) (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (J : (⋃ i, B i) ≃ₜ (⋃ i, B i)) (hJ : Function.Involutive J)
    (hvalue : ∀ i (x : B i),
      (J ⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩ : E) = prismFiberReflection (H i) x) :
    ∃ (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
      (hτ : Function.Involutive τ),
      (∀ x, τ x ≠ x) ∧
      (∀ x, (τ x : E) = J ⟨x,by
        obtain ⟨i,hi⟩ := mem_iUnion.mp x.property
        exact mem_iUnion.mpr ⟨i,prismEnds_subset (H i) hi⟩⟩) ∧
      (∀ i (x : A i) (b : Bool),
        (τ ⟨prismEndMap (H i) x b,
          mem_iUnion.mpr ⟨i,⟨(x,b),rfl⟩⟩⟩ : E) = prismEndMap (H i) x (!b)) ∧
      IsCoveringMap (FreeInvolutionQuotient.projection τ hτ) ∧
      (∀ x, FreeInvolutionQuotient.projection τ hτ ⁻¹'
        {FreeInvolutionQuotient.projection τ hτ x} = {x,τ x}) := by
  let C := ⋃ i, prismEnds (H i)
  have hCB : C ⊆ ⋃ i, B i := iUnion_mono (fun i => prismEnds_subset (H i))
  have hmap (x : (⋃ i, B i : Set E)) (hx : (x : E) ∈ C) : (J x : E) ∈ C := by
    obtain ⟨i,⟨z,hzx⟩⟩ := mem_iUnion.mp hx
    have hxx : x = ⟨prismEndMap (H i) z.1 z.2,
        mem_iUnion.mpr ⟨i,(prismEndMap (H i) z.1 z.2).property⟩⟩ := Subtype.ext hzx.symm
    rw [hxx,hvalue,prismFiberReflection_end]
    exact mem_iUnion.mpr ⟨i,⟨(z.1,!z.2),rfl⟩⟩
  have hiff (x : (⋃ i, B i : Set E)) : (x : E) ∈ C ↔ (J x : E) ∈ C := by
    refine ⟨hmap x,fun hx => ?_⟩
    simpa only [hJ x] using hmap (J x) hx
  let τ : C ≃ₜ C := J.restrictSubsets hCB hCB hiff
  have hτval (x : C) : (τ x : E) = J ⟨x,hCB x.property⟩ := rfl
  have hτ : Function.Involutive τ := by
    intro x
    apply Subtype.ext
    change (J (J ⟨x,hCB x.property⟩) : E) = x
    rw [hJ]
  have hends (i : ι) (x : A i) (b : Bool) :
      (τ ⟨prismEndMap (H i) x b,mem_iUnion.mpr ⟨i,⟨(x,b),rfl⟩⟩⟩ : E) =
        prismEndMap (H i) x (!b) := by
    rw [hτval,hvalue,prismFiberReflection_end]
  have hfree (x : C) : τ x ≠ x := by
    obtain ⟨i,⟨z,hzx⟩⟩ := mem_iUnion.mp x.property
    intro h
    have hx : x = ⟨prismEndMap (H i) z.1 z.2,mem_iUnion.mpr ⟨i,⟨z,rfl⟩⟩⟩ :=
      Subtype.ext hzx.symm
    have hh := congrArg (fun y : C => (y : E)) h
    rw [hx,hends] at hh
    exact prismEndMap_flip_ne (H i) z.1 z.2 (Subtype.ext hh)
  refine ⟨τ,hτ,hfree,hτval,hends,
    FreeInvolutionQuotient.projection_isCoveringMap τ hτ hfree,?_⟩
  intro x
  ext y
  exact FreeInvolutionQuotient.projection_eq τ hτ y x

end PoincareConjecture.M76.PrismBelt
