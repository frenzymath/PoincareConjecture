import PoincareConjecture.Proofs.M11.TimeRestriction





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}

noncomputable def worldlineTimeRestrict (S : SpacetimeIntervalSystem)
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (γ : SpacetimeWorldline F (S.interval K)) : SpacetimeWorldline F (S.interval L) where
  interval_subset := fun _ ht ↦ γ.interval_subset (h ht)
  curve := γ.curve ∘ spacetimeIntervalInclusion (S.interval L) (S.interval K) h
  smooth := γ.smooth.comp (S.inclusion_smooth L K h)
  time_eq := fun t ↦ γ.time_eq
    (spacetimeIntervalInclusion (S.interval L) (S.interval K) h t)
  derivative_eq := by
    intro t
    have hc := mfderiv_comp_apply t
      ((γ.smooth _).mdifferentiableAt (by simp))
      ((S.inclusion_smooth L K h t).mdifferentiableAt (by simp))
      ((S.interval L).positiveTangent t)
    rw [S.inclusion_derivative, γ.derivative_eq] at hc
    exact hc

noncomputable def embeddingWorldline {K : SpacetimeInterval} {D : SmoothSpacetimeInterval K}
    {C : Type*} [TopologicalSpace C] (e : CompatibleSpacetimeEmbedding F D C) (x : C) :
    SpacetimeWorldline F D where
  interval_subset := e.interval_subset
  curve := fun t ↦ e.toSpacetime (t, x)
  smooth := e.worldline_smooth x
  time_eq := fun t ↦ e.time_eq (t, x)
  derivative_eq := fun t ↦ e.worldline_derivative t x

end PoincareConjecture.Proofs.M11
