import PoincareConjecture.Proofs.M13.Domains








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}
  {P : ParabolicSpacetimeRescaling R Q hQ a}

theorem intervalTransport_inverse_inclusion
    (T : ParabolicIntervalTransport R.timeIntervals Q hQ a)
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a L)).Point) :
    (T.diffeomorph K).symm (spacetimeIntervalInclusion _ _
      (parabolicInterval_subset Q hQ a L K h) s) =
        spacetimeIntervalInclusion _ _ h ((T.diffeomorph L).symm s) := by
  apply Subtype.ext
  simp only [T.inverse_eq]
  rfl

theorem intervalTransport_forward_inclusion
    (T : ParabolicIntervalTransport R.timeIntervals Q hQ a)
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (s : (R.timeIntervals.interval L).Point) :
    T.diffeomorph K (spacetimeIntervalInclusion _ _ h s) =
      spacetimeIntervalInclusion _ _ (parabolicInterval_subset Q hQ a L K h)
        (T.diffeomorph L s) := by
  apply Subtype.ext
  simp only [T.forward_eq]
  rfl

theorem domain_worldline_image (D : ParabolicDomainTransport.{u, v} P)
    (K : SpacetimeInterval)
    (e : SpacetimeWorldline R.spacetime (R.timeIntervals.interval K)) :
    Set.range (D.worldlineEquiv K e).curve = Set.range e.curve := by
  have h : (D.worldlineEquiv K e).curve = e.curve ∘ (P.intervalTransport.diffeomorph K).symm :=
    funext (D.worldline_forward K e)
  rw [h]
  exact (P.intervalTransport.diffeomorph K).symm.surjective.range_comp e.curve

theorem domain_embedding_image (D : ParabolicDomainTransport.{u, v} P)
    (C : Type v) [TopologicalSpace C] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C) :
    Set.range (D.embeddingEquiv C K e).toSpacetime = Set.range e.toSpacetime := by
  ext p
  constructor
  · rintro ⟨⟨t, x⟩, rfl⟩
    exact ⟨((P.intervalTransport.diffeomorph K).symm t, x),
      (D.embedding_forward C K e t x).symm⟩
  · rintro ⟨⟨t, x⟩, rfl⟩
    refine ⟨(P.intervalTransport.diffeomorph K t, x), ?_⟩
    rw [D.embedding_forward, Diffeomorph.symm_apply_apply]

theorem domain_cylinder_image (D : ParabolicDomainTransport.{u, v} P)
    (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C) :
    Set.range (D.cylinderEquiv C K e).toSpacetime = Set.range e.toSpacetime := by
  have h := domain_embedding_image D C K e.toCompatibleSpacetimeEmbedding
  rw [← D.cylinder_embedding] at h
  exact h

theorem domain_embedding_based (D : ParabolicDomainTransport.{u, v} P)
    (C : Type v) [TopologicalSpace C] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C)
    (t : (R.timeIntervals.interval K).Point) (source : C → R.spacetime.Point) :
    (D.embeddingEquiv C K e).IsBasedAt (P.intervalTransport.diffeomorph K t) source ↔
      e.IsBasedAt t source := by
  unfold CompatibleSpacetimeEmbedding.IsBasedAt
  simp only [D.embedding_forward, Diffeomorph.symm_apply_apply]

theorem domain_cylinder_based (D : ParabolicDomainTransport.{u, v} P)
    (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C)
    (t : (R.timeIntervals.interval K).Point) (source : C → R.spacetime.Point) :
    (D.cylinderEquiv C K e).toCompatibleSpacetimeEmbedding.IsBasedAt
        (P.intervalTransport.diffeomorph K t) source ↔
      e.toCompatibleSpacetimeEmbedding.IsBasedAt t source := by
  rw [D.cylinder_embedding]
  exact domain_embedding_based D C K e.toCompatibleSpacetimeEmbedding t source

theorem domain_worldline_restrict (D : ParabolicDomainTransport.{u, v} P)
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (e : SpacetimeWorldline R.spacetime (R.timeIntervals.interval K))
    (r : SpacetimeWorldline R.spacetime (R.timeIntervals.interval L))
    (hr : ∀ t, r.curve t = e.curve (spacetimeIntervalInclusion _ _ h t))
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a L)).Point) :
    (D.worldlineEquiv L r).curve s = (D.worldlineEquiv K e).curve
      (spacetimeIntervalInclusion _ _ (parabolicInterval_subset Q hQ a L K h) s) := by
  rw [D.worldline_forward, D.worldline_forward, hr, intervalTransport_inverse_inclusion]

theorem domain_embedding_restrict (D : ParabolicDomainTransport.{u, v} P)
    (C : Type v) [TopologicalSpace C] (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C)
    (r : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval L) C)
    (hr : ∀ t x, r.toSpacetime (t, x) = e.toSpacetime (spacetimeIntervalInclusion _ _ h t, x))
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a L)).Point) (x : C) :
    (D.embeddingEquiv C L r).toSpacetime (s, x) = (D.embeddingEquiv C K e).toSpacetime
      (spacetimeIntervalInclusion _ _ (parabolicInterval_subset Q hQ a L K h) s, x) := by
  rw [D.embedding_forward, D.embedding_forward, hr, intervalTransport_inverse_inclusion]

theorem domain_cylinder_restrict (D : ParabolicDomainTransport.{u, v} P)
    (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C)
    (r : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval L) C)
    (hr : ∀ t x, r.toSpacetime (t, x) = e.toSpacetime (spacetimeIntervalInclusion _ _ h t, x))
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a L)).Point) (x : C) :
    (D.cylinderEquiv C L r).toSpacetime (s, x) = (D.cylinderEquiv C K e).toSpacetime
      (spacetimeIntervalInclusion _ _ (parabolicInterval_subset Q hQ a L K h) s, x) := by
  rw [D.cylinder_forward, D.cylinder_forward, hr, intervalTransport_inverse_inclusion]

end PoincareConjecture.M13
