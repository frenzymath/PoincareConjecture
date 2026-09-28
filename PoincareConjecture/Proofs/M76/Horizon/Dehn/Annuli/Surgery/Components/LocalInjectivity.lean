import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.RawChart
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.ClosedSeamLocalInjectivity
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.Counts

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem isLocallyInjective_of_raw_source_crossings
    {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X} {S : Set E} {R : Set X}
    (hG : IsClosed (doubleLocusOn f S))
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y)) :
    IsLocallyInjective (fun x : S ↦ f x) := by
  classical
  intro x
  by_cases hx : (x : E) ∈ doubleLocusOn f S
  · obtain ⟨y, hy, hxy, hne⟩ := hx.2
    obtain ⟨C⟩ := hcross x x.property y hy hne hxy
    have hbranch (A : Set E) (hAo : IsOpen ((Subtype.val : S → E) ⁻¹' A))
        (hxA : (x : E) ∈ A) (he : IsEmbedding (fun z : A ↦ f z)) :
        ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ InjOn (fun z : S ↦ f z) U := by
      refine ⟨Subtype.val ⁻¹' A, hAo, hxA, ?_⟩
      intro z hz w hw hzw
      exact Subtype.ext (congrArg (fun t : A ↦ (t : E)) (he.injective
        (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw))
    rcases C.labels with h | h
    · exact hbranch C.left C.left_open h.1 C.left_embedding
    · exact hbranch C.right C.right_open h.1 C.right_embedding
  · refine ⟨Subtype.val ⁻¹' (doubleLocusOn f S)ᶜ,
      hG.isOpen_compl.preimage continuous_subtype_val, hx, ?_⟩
    intro z hz w hw hzw
    apply Subtype.ext
    by_contra hne
    exact hz ⟨z.property, w, w.property, hzw, hne⟩

end PoincareConjecture.M76.Dehn.Annuli
