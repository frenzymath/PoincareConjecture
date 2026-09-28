import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.OrdinaryModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.ClosedSeamLocalInjectivity

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem OrdinaryDoubleCurveModel.isLocallyInjective
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) :
    IsLocallyInjective (fun x : D2 => f x) := by
  classical
  let : Finite old.Index := old.finiteIndex
  have hG : IsClosed (doubleLocusOn f D2) := by
    rw [← old.cover]
    exact (isCompact_iUnion old.compact).isClosed
  intro x
  by_cases hx : (x : V2) ∈ doubleLocusOn f D2
  · obtain ⟨y, hy, hxy, hne⟩ := hx.2
    obtain ⟨C⟩ := old.crossings x x.property y hy hne hxy
    have hbranch (A : Set V2) (hAo : IsOpen ((Subtype.val : D2 → V2) ⁻¹' A))
        (hxA : (x : V2) ∈ A) (he : IsEmbedding (fun z : A => f z)) :
        ∃ U : Set D2, IsOpen U ∧ x ∈ U ∧ InjOn (fun z : D2 => f z) U := by
      refine ⟨Subtype.val ⁻¹' A, hAo, hxA, ?_⟩
      intro z hz w hw hzw
      exact Subtype.ext (congrArg (fun t : A => (t : V2)) (he.injective
        (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw))
    rcases C.labels with h | h
    · exact hbranch C.left C.left_open h.1 C.left_embedding
    · exact hbranch C.right C.right_open h.1 C.right_embedding
  · refine ⟨Subtype.val ⁻¹' (doubleLocusOn f D2)ᶜ,
      hG.isOpen_compl.preimage continuous_subtype_val, hx, ?_⟩
    intro z hz w hw hzw
    apply Subtype.ext
    by_contra hne
    exact hz ⟨z.property, w, w.property, hzw, hne⟩

end PoincareConjecture.M76.Dehn
