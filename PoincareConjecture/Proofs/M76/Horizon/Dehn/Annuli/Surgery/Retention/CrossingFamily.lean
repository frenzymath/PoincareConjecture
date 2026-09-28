import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CrossingTransport

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)



theorem raw_source_crossings_of_retained_open_copy
    {E Y X ι : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {g : Y → X}
    {S U : Set E} {T V : Set Y} {R : Set X}
    (hS : IsCompact S) (hT : IsCompact T) (hUS : U ⊆ S) (hVT : V ⊆ T)
    (hU : IsOpen ((Subtype.val : S → E) ⁻¹' U))
    (hV : IsOpen ((Subtype.val : T → Y) ⁻¹' V))
    (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (H : U ≃ₜ V) (hkeep : ∀ x : U, g (H x) = f x)
    (p : doubleLocusOn f S → doubleLocusOn f S)
    (hunique : ∀ (x : doubleLocusOn f S) (y : E), y ∈ S →
      f x = f y → (x : E) ≠ y → y = (p x : E))
    (hcontains : doubleLocusOn g T ⊆ V)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x ≠ y →
      Nonempty (RawSourceCrossing e f S R x y)) :
    ∀ x ∈ T, ∀ y ∈ T, g x = g y → x ≠ y →
      Nonempty (RawSourceCrossing e g T R x y) := by
  intro x hx y hy hxy hne
  have hxV : x ∈ V := hcontains ⟨hx, y, hy, hxy, hne⟩
  have hyV : y ∈ V := hcontains ⟨hy, x, hx, hxy.symm, Ne.symm hne⟩
  let a : U := H.symm ⟨x, hxV⟩
  let b : U := H.symm ⟨y, hyV⟩
  have ha : (H a : Y) = x := congrArg Subtype.val (H.apply_symm_apply _)
  have hb : (H b : Y) = y := congrArg Subtype.val (H.apply_symm_apply _)
  have hab : f a = f b := by
    rw [← hkeep a, ← hkeep b, ha, hb]
    exact hxy
  have habne : (a : E) ≠ b := by
    intro hh
    have heq := congrArg (fun z : U ↦ (H z : Y)) (Subtype.ext hh)
    exact hne (ha.symm.trans (heq.trans hb))
  obtain ⟨C⟩ := hcross a (hUS a.property) b (hUS b.property) hab habne
  obtain ⟨C', _⟩ := C.transport_retained hS hT hUS hVT hU hV hf hg H hkeep
    p hunique hcontains a b hab habne univ isOpen_univ (mem_univ _)
  rw [ha, hb] at C'
  exact ⟨C'⟩

end PoincareConjecture.M76.Dehn.Annuli
