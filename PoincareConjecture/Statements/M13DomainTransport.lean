import PoincareConjecture.Definitions.M13DomainTransport











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}
  {P : ParabolicSpacetimeRescaling R Q hQ a}


structure ParabolicDomainCalculus (D : ParabolicDomainTransport.{u, v} P) : Prop where
  worldline_image : ∀ (K : SpacetimeInterval)
    (γ : SpacetimeWorldline R.spacetime (R.timeIntervals.interval K)),
    Set.range (D.worldlineEquiv K γ).curve = Set.range γ.curve
  embedding_image : ∀ (C : Type v) [TopologicalSpace C] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C),
    Set.range (D.embeddingEquiv C K e).toSpacetime = Set.range e.toSpacetime
  cylinder_image : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C),
    Set.range (D.cylinderEquiv C K e).toSpacetime = Set.range e.toSpacetime
  embedding_based : ∀ (C : Type v) [TopologicalSpace C] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C)
    (t : (R.timeIntervals.interval K).Point) (source : C → R.spacetime.Point),
    (D.embeddingEquiv C K e).IsBasedAt (P.intervalTransport.diffeomorph K t) source ↔
      e.IsBasedAt t source
  cylinder_based : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C)
    (t : (R.timeIntervals.interval K).Point) (source : C → R.spacetime.Point),
    (D.cylinderEquiv C K e).toCompatibleSpacetimeEmbedding.IsBasedAt
        (P.intervalTransport.diffeomorph K t) source ↔
      e.toCompatibleSpacetimeEmbedding.IsBasedAt t source
  worldline_time_restrict : ∀ (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (γ : SpacetimeWorldline R.spacetime (R.timeIntervals.interval K))
    (η : SpacetimeWorldline R.spacetime (R.timeIntervals.interval L)),
    (∀ t : (R.timeIntervals.interval L).Point,
      η.curve t = γ.curve (spacetimeIntervalInclusion
        (R.timeIntervals.interval L) (R.timeIntervals.interval K) h t)) →
    ∀ s : (R.timeIntervals.interval (parabolicInterval Q hQ a L)).Point,
      (D.worldlineEquiv L η).curve s = (D.worldlineEquiv K γ).curve
        (spacetimeIntervalInclusion
          (R.timeIntervals.interval (parabolicInterval Q hQ a L))
          (R.timeIntervals.interval (parabolicInterval Q hQ a K))
          (parabolicInterval_subset Q hQ a L K h) s)
  embedding_time_restrict : ∀ (C : Type v) [TopologicalSpace C]
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C)
    (r : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval L) C),
    (∀ (t : (R.timeIntervals.interval L).Point) (x : C),
      r.toSpacetime (t, x) = e.toSpacetime
        (spacetimeIntervalInclusion
          (R.timeIntervals.interval L) (R.timeIntervals.interval K) h t, x)) →
    ∀ (s : (R.timeIntervals.interval (parabolicInterval Q hQ a L)).Point) (x : C),
      (D.embeddingEquiv C L r).toSpacetime (s, x) = (D.embeddingEquiv C K e).toSpacetime
        (spacetimeIntervalInclusion
          (R.timeIntervals.interval (parabolicInterval Q hQ a L))
          (R.timeIntervals.interval (parabolicInterval Q hQ a K))
          (parabolicInterval_subset Q hQ a L K h) s, x)
  cylinder_time_restrict : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C)
    (r : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval L) C),
    (∀ (t : (R.timeIntervals.interval L).Point) (x : C),
      r.toSpacetime (t, x) = e.toSpacetime
        (spacetimeIntervalInclusion
          (R.timeIntervals.interval L) (R.timeIntervals.interval K) h t, x)) →
    ∀ (s : (R.timeIntervals.interval (parabolicInterval Q hQ a L)).Point) (x : C),
      (D.cylinderEquiv C L r).toSpacetime (s, x) = (D.cylinderEquiv C K e).toSpacetime
        (spacetimeIntervalInclusion
          (R.timeIntervals.interval (parabolicInterval Q hQ a L))
          (R.timeIntervals.interval (parabolicInterval Q hQ a K))
          (parabolicInterval_subset Q hQ a L K h) s, x)
  embedding_source_restrict : ∀ (C C' : Type v)
    [TopologicalSpace C] [TopologicalSpace C'] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C)
    (r : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C') (j : C' → C),
    (∀ (t : (R.timeIntervals.interval K).Point) (x : C'),
      r.toSpacetime (t, x) = e.toSpacetime (t, j x)) →
    ∀ (s : (R.timeIntervals.interval (parabolicInterval Q hQ a K)).Point) (x : C'),
      (D.embeddingEquiv C' K r).toSpacetime (s, x) = (D.embeddingEquiv C K e).toSpacetime (s, j x)
  cylinder_open_restrict : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C)
    (U : TopologicalSpace.Opens C)
    (r : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) U),
    (∀ (t : (R.timeIntervals.interval K).Point) (x : U),
      r.toSpacetime (t, x) = e.toSpacetime (t, x.val)) →
    ∀ (s : (R.timeIntervals.interval (parabolicInterval Q hQ a K)).Point) (x : U),
      (D.cylinderEquiv U K r).toSpacetime (s, x) = (D.cylinderEquiv C K e).toSpacetime (s, x.val)
  relative_time_open_iff : ∀ K L : SpacetimeInterval,
    IsOpen {s : (parabolicInterval Q hQ a K).domain |
        s.val ∈ (parabolicInterval Q hQ a L).domain} ↔
      IsOpen {t : K.domain | t.val ∈ L.domain}
  time_cover_iff : ∀ (K : SpacetimeInterval) (B : Type u) (J : B → SpacetimeInterval),
    (∀ s : (parabolicInterval Q hQ a K).domain,
      ∃ b : B, s.val ∈ (parabolicInterval Q hQ a (J b)).domain) ↔
      ∀ t : K.domain, ∃ b : B, t.val ∈ (J b).domain
  cylinder_glue : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (B : Type u) (J : B → SpacetimeInterval)
    (h : ∀ b, (J b).domain ⊆ K.domain)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C)
    (localCylinder : ∀ b, CompatibleSpacetimeCylinder R.spacetime
      (R.timeIntervals.interval (J b)) C),
    (∀ (b : B) (t : (R.timeIntervals.interval (J b)).Point) (x : C),
      e.toSpacetime (spacetimeIntervalInclusion
        (R.timeIntervals.interval (J b)) (R.timeIntervals.interval K) (h b) t, x) =
        (localCylinder b).toSpacetime (t, x)) →
    ∀ (b : B) (s : (R.timeIntervals.interval (parabolicInterval Q hQ a (J b))).Point) (x : C),
      (D.cylinderEquiv C K e).toSpacetime (spacetimeIntervalInclusion
        (R.timeIntervals.interval (parabolicInterval Q hQ a (J b)))
        (R.timeIntervals.interval (parabolicInterval Q hQ a K))
        (parabolicInterval_subset Q hQ a (J b) K (h b)) s, x) =
        (D.cylinderEquiv C (J b) (localCylinder b)).toSpacetime (s, x)
  worldline_maximal_iff : ∀ (K : SpacetimeInterval)
    (γ : SpacetimeWorldline R.spacetime (R.timeIntervals.interval K)),
    (D.worldlineEquiv K γ).IsMaximal R.timeIntervals ↔ γ.IsMaximal R.timeIntervals
  embedding_maximal_iff : ∀ (C : Type v) [TopologicalSpace C] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C),
    (D.embeddingEquiv C K e).IsMaximal R.timeIntervals ↔ e.IsMaximal R.timeIntervals
  cylinder_metric_exists : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C),
    Nonempty (SpacetimeCylinderMetric (D.cylinderEquiv C K e))
  cylinder_metric : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C)
    (g : SpacetimeCylinderMetric e) (h : SpacetimeCylinderMetric (D.cylinderEquiv C K e))
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a K)).Point)
    (x : C) (u v : TangentSpace (𝓡 n) x),
    (h.metric s.val).inner x u v =
      Q * (g.metric (parabolicTimeInv Q a s.val)).inner x u v

end PoincareConjecture
