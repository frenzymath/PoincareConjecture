import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CrossingFamily

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli



theorem reflection_open_retained_source
    {E X : Type*} [TopologicalSpace E] {f g : E → X} {S T C : Set E}
    (hT : IsClosed T) (htrace : doubleLocusOn f S ∩ T = C)
    (hinside : C ⊆ interior T) (hkeep : EqOn g f (S \ interior T))
    (hnew : doubleLocusOn g S = doubleLocusOn f (S \ interior T)) :
    IsOpen ((Subtype.val : S → E) ⁻¹' (S \ T)) ∧
      EqOn g f (S \ T) ∧ doubleLocusOn g S ⊆ S \ T := by
  have hopen : IsOpen ((Subtype.val : S → E) ⁻¹' (S \ T)) := by
    have heq : (Subtype.val : S → E) ⁻¹' (S \ T) =
        ((Subtype.val : S → E) ⁻¹' T)ᶜ := by
      ext x
      exact and_iff_right x.property
    rw [heq]
    exact (hT.preimage continuous_subtype_val).isOpen_compl
  refine ⟨hopen, fun x hx ↦ hkeep ⟨hx.1, fun h ↦ hx.2 (interior_subset h)⟩, ?_⟩
  intro x hx
  obtain ⟨hxK, y, hyK, hxy, hne⟩ := hnew.subset hx
  refine ⟨hxK.1, ?_⟩
  intro hxT
  exact hxK.2 (hinside (htrace.subset ⟨⟨hxK.1, y, hyK.1, hxy, hne⟩, hxT⟩))



theorem reflection_raw_source_crossings
    {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f g : E → X}
    {S T C : Set E} {R : Set X}
    (hS : IsCompact S) (hT : IsClosed T)
    (htrace : doubleLocusOn f S ∩ T = C) (hinside : C ⊆ interior T)
    (hkeep : EqOn g f (S \ interior T))
    (hnew : doubleLocusOn g S = doubleLocusOn f (S \ interior T))
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (p : doubleLocusOn f S → doubleLocusOn f S)
    (hunique : ∀ (x : doubleLocusOn f S) (y : E), y ∈ S →
      f x = f y → (x : E) ≠ y → y = (p x : E))
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y)) :
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → g x = g y →
      Nonempty (RawSourceCrossing e g S R x y) := by
  obtain ⟨hopen, hkeep', hcontains⟩ :=
    reflection_open_retained_source hT htrace hinside hkeep hnew
  intro x hx y hy hne hxy
  exact raw_source_crossings_of_retained_open_copy hS hS sdiff_subset sdiff_subset
    hopen hopen hf hg (Homeomorph.refl ↥(S \ T : Set E)) (fun x ↦ hkeep' x.property)
    p hunique hcontains (fun a ha b hb hab hne ↦ hcross a ha b hb hne hab)
    x hx y hy hxy hne

end PoincareConjecture.M76.Dehn.Annuli
