import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Domain.Laws










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}
  {P : ParabolicSpacetimeRescaling R Q hQ a}

theorem domain_worldline_maximal (D : ParabolicDomainTransport.{u, v} P)
    (K : SpacetimeInterval)
    (e : SpacetimeWorldline R.spacetime (R.timeIntervals.interval K)) :
    (D.worldlineEquiv K e).IsMaximal R.timeIntervals ↔ e.IsMaximal R.timeIntervals := by
  constructor
  · intro H L f h hf
    apply interval_subset_of_parabolic (Q := Q) (hQ := hQ) (a := a)
    apply H (parabolicInterval Q hQ a L) (D.worldlineEquiv L f)
      (parabolicInterval_subset Q hQ a K L h)
    intro s
    exact (domain_worldline_restrict D L K h f e (fun t ↦ (hf t).symm) s).symm
  · intro H L
    obtain ⟨L, rfl⟩ := parabolicInterval_surjective Q hQ a L
    intro f h hf
    let h₀ : K.domain ⊆ L.domain := interval_subset_of_parabolic h
    have hf₀ : ∀ t : (R.timeIntervals.interval K).Point,
        ((D.worldlineEquiv L).symm f).curve (spacetimeIntervalInclusion _ _ h₀ t) =
          e.curve t := by
      intro t
      rw [D.worldline_inverse, intervalTransport_forward_inclusion]
      have hval := hf (P.intervalTransport.diffeomorph K t)
      rw [D.worldline_forward, Diffeomorph.symm_apply_apply] at hval
      exact hval
    exact parabolicInterval_subset Q hQ a L K
      (H L ((D.worldlineEquiv L).symm f) h₀ hf₀)

theorem domain_embedding_maximal (D : ParabolicDomainTransport.{u, v} P)
    (C : Type v) [TopologicalSpace C] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C) :
    (D.embeddingEquiv C K e).IsMaximal R.timeIntervals ↔ e.IsMaximal R.timeIntervals := by
  constructor
  · intro H L f h hf
    apply interval_subset_of_parabolic (Q := Q) (hQ := hQ) (a := a)
    apply H (parabolicInterval Q hQ a L) (D.embeddingEquiv C L f)
      (parabolicInterval_subset Q hQ a K L h)
    intro s x
    exact (domain_embedding_restrict D C L K h f e (fun t y ↦ (hf t y).symm) s x).symm
  · intro H L
    obtain ⟨L, rfl⟩ := parabolicInterval_surjective Q hQ a L
    intro f h hf
    let h₀ : K.domain ⊆ L.domain := interval_subset_of_parabolic h
    have hf₀ : ∀ (t : (R.timeIntervals.interval K).Point) (x : C),
        ((D.embeddingEquiv C L).symm f).toSpacetime
            (spacetimeIntervalInclusion _ _ h₀ t, x) = e.toSpacetime (t, x) := by
      intro t x
      rw [D.embedding_inverse, intervalTransport_forward_inclusion]
      have hval := hf (P.intervalTransport.diffeomorph K t) x
      rw [D.embedding_forward, Diffeomorph.symm_apply_apply] at hval
      exact hval
    exact parabolicInterval_subset Q hQ a L K
      (H L ((D.embeddingEquiv C L).symm f) h₀ hf₀)

end PoincareConjecture.ParabolicRescaling
