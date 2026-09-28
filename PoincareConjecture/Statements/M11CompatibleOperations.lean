import PoincareConjecture.Definitions.M11CompatibleEmbedding

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

structure CompatibleSpacetimeTheory {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I : SpacetimeInterval}
    (F : GeneralizedFlowSpacetime n X time I) (D : SpacetimeIntervalSystem) : Prop where

  worldline_unique : ∀ (K L : SpacetimeInterval)
    (γ : SpacetimeWorldline F (D.interval K))
    (η : SpacetimeWorldline F (D.interval L))
    (t₀ : ℝ) (hK : t₀ ∈ K.domain) (hL : t₀ ∈ L.domain),
    γ.curve ⟨t₀, hK⟩ = η.curve ⟨t₀, hL⟩ →
    ∀ (t : ℝ) (htK : t ∈ K.domain) (htL : t ∈ L.domain),
      γ.curve ⟨t, htK⟩ = η.curve ⟨t, htL⟩

  embedding_unique : ∀ (C : Type v) [TopologicalSpace C]
    (K L : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding F (D.interval K) C)
    (f : CompatibleSpacetimeEmbedding F (D.interval L) C)
    (t₀ : ℝ) (hK : t₀ ∈ K.domain) (hL : t₀ ∈ L.domain)
    (source : C → F.Point),
    e.IsBasedAt ⟨t₀, hK⟩ source → f.IsBasedAt ⟨t₀, hL⟩ source →
    ∀ (t : ℝ) (htK : t ∈ K.domain) (htL : t ∈ L.domain) (x : C),
      e.toSpacetime (⟨t, htK⟩, x) = f.toSpacetime (⟨t, htL⟩, x)

  embedding_time_restrict : ∀ (C : Type v) [TopologicalSpace C]
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (e : CompatibleSpacetimeEmbedding F (D.interval K) C),
    ∃ r : CompatibleSpacetimeEmbedding F (D.interval L) C,
      ∀ (t : (D.interval L).Point) (x : C),
        r.toSpacetime (t, x) =
          e.toSpacetime (spacetimeIntervalInclusion (D.interval L) (D.interval K) h t, x)

  cylinder_time_restrict : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K L : SpacetimeInterval) (h : L.domain ⊆ K.domain)
    (e : CompatibleSpacetimeCylinder F (D.interval K) C),
    ∃ r : CompatibleSpacetimeCylinder F (D.interval L) C,
      ∀ (t : (D.interval L).Point) (x : C),
        r.toSpacetime (t, x) =
          e.toSpacetime (spacetimeIntervalInclusion (D.interval L) (D.interval K) h t, x)

  embedding_source_restrict : ∀ (C C' : Type v)
    [TopologicalSpace C] [TopologicalSpace C'] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding F (D.interval K) C)
    (j : C' → C), Topology.IsEmbedding j →
    ∃ r : CompatibleSpacetimeEmbedding F (D.interval K) C',
      ∀ (t : (D.interval K).Point) (x : C'),
        r.toSpacetime (t, x) = e.toSpacetime (t, j x)

  cylinder_open_restrict : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (e : CompatibleSpacetimeCylinder F (D.interval K) C)
    (U : TopologicalSpace.Opens C),
    ∃ r : CompatibleSpacetimeCylinder F (D.interval K) U,
      ∀ (t : (D.interval K).Point) (x : U),
        r.toSpacetime (t, x) = e.toSpacetime (t, x.val)

  cylinder_glue : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (B : Type u) (J : B → SpacetimeInterval)
    (hsubset : ∀ b, (J b).domain ⊆ K.domain),
    (∀ b, IsOpen {t : K.domain | t.val ∈ (J b).domain}) →
    (∀ t : K.domain, ∃ b, t.val ∈ (J b).domain) →
    ∀ (localCylinder : ∀ b, CompatibleSpacetimeCylinder F (D.interval (J b)) C),
    (∀ (b c : B) (t : ℝ) (hb : t ∈ (J b).domain) (hc : t ∈ (J c).domain) (x : C),
      (localCylinder b).toSpacetime (⟨t, hb⟩, x) =
        (localCylinder c).toSpacetime (⟨t, hc⟩, x)) →
    ∃ e : CompatibleSpacetimeCylinder F (D.interval K) C,
      (∀ (b : B) (t : (D.interval (J b)).Point) (x : C),
        e.toSpacetime
            (spacetimeIntervalInclusion (D.interval (J b)) (D.interval K) (hsubset b) t, x) =
          (localCylinder b).toSpacetime (t, x)) ∧
      (∀ (b : B) (t₀ : (D.interval (J b)).Point) (source : C → F.Point),
        (localCylinder b).toCompatibleSpacetimeEmbedding.IsBasedAt t₀ source →
        e.toCompatibleSpacetimeEmbedding.IsBasedAt
          (spacetimeIntervalInclusion (D.interval (J b)) (D.interval K) (hsubset b) t₀)
          source)

  cylinder_metric : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (e : CompatibleSpacetimeCylinder F (D.interval K) C),
    Nonempty (SpacetimeCylinderMetric e)

end PoincareConjecture
