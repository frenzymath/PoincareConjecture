import PoincareLib.Geometry.Spacetime.Rescaling.Basic

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M13DomainTransport.lean`,
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Declaration bodies are unchanged; only imports and module placement differ. -/

/-!
# Actual parabolic transport of compatible domains

Morgan-Tian Definitions 3.38, 3.40 and 3.41, pp. 61-62. These output
records keep the supplied maps, their exact intervals and their source
inclusions. Maximality is an explicit conditional property of an existing
domain, not a claim of a common lifetime for a noncompact source.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X]

/-- An existing worldline has no extension to a larger interval in this
spacetime. The extension must agree on the entire original domain. -/
def SpacetimeWorldline.IsMaximal {time : X → ℝ} {I K : SpacetimeInterval}
    {F : GeneralizedFlowSpacetime n X time I} (T : SpacetimeIntervalSystem)
    (γ : SpacetimeWorldline F (T.interval K)) : Prop :=
  ∀ (L : SpacetimeInterval) (η : SpacetimeWorldline F (T.interval L))
    (h : K.domain ⊆ L.domain),
    (∀ t : (T.interval K).Point,
      η.curve (spacetimeIntervalInclusion (T.interval K) (T.interval L) h t) = γ.curve t) →
    L.domain ⊆ K.domain

/-- Maximality of an actual compatible embedding for its fixed spatial
source. No existence or openness of such a maximal interval is asserted. -/
def CompatibleSpacetimeEmbedding.IsMaximal {time : X → ℝ} {I K : SpacetimeInterval}
    {F : GeneralizedFlowSpacetime n X time I} (T : SpacetimeIntervalSystem)
    {C : Type v} [TopologicalSpace C]
    (e : CompatibleSpacetimeEmbedding F (T.interval K) C) : Prop :=
  ∀ (L : SpacetimeInterval) (f : CompatibleSpacetimeEmbedding F (T.interval L) C)
    (h : K.domain ⊆ L.domain),
    (∀ (t : (T.interval K).Point) (x : C),
      f.toSpacetime (spacetimeIntervalInclusion (T.interval K) (T.interval L) h t, x) =
        e.toSpacetime (t, x)) →
    L.domain ⊆ K.domain

/-- A compatible neighborhood with the actual open initial metric ball as
source. Its base time lies in K and its base map is the literal slice
inclusion. Closed or half-open time domains are separate explicit conditions. -/
structure BasedBallSpacetimeNeighborhood {time : X → ℝ} {I : SpacetimeInterval}
    (F : GeneralizedFlowSpacetime n X time I)
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (T : SpacetimeIntervalSystem)
    (t : ℝ) (p : (S t).Point) (r : ℝ) (K : SpacetimeInterval) where
  radius_pos : 0 < r
  base_mem : t ∈ K.domain
  embedding : CompatibleSpacetimeEmbedding F (T.interval K) ((S t).metricOnPoints.ball p r)
  based : embedding.IsBasedAt ⟨t, base_mem⟩ (fun x ↦ x.val.val)

variable {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

/-- Equivalences of actual compatible map records under the affine clock.
The displayed point identities prescribe both directions, on exactly K and
its affine image, using one fixed interval system. -/
structure ParabolicDomainTransport (P : ParabolicSpacetimeRescaling R Q hQ a) where
  worldlineEquiv : ∀ K : SpacetimeInterval,
    SpacetimeWorldline R.spacetime (R.timeIntervals.interval K) ≃
      SpacetimeWorldline P.realization.spacetime
        (R.timeIntervals.interval (parabolicInterval Q hQ a K))
  worldline_forward : ∀ (K : SpacetimeInterval)
    (γ : SpacetimeWorldline R.spacetime (R.timeIntervals.interval K))
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a K)).Point),
    (worldlineEquiv K γ).curve s = γ.curve ((P.intervalTransport.diffeomorph K).symm s)
  worldline_inverse : ∀ (K : SpacetimeInterval)
    (γ : SpacetimeWorldline P.realization.spacetime
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)))
    (t : (R.timeIntervals.interval K).Point),
    ((worldlineEquiv K).symm γ).curve t = γ.curve (P.intervalTransport.diffeomorph K t)
  embeddingEquiv : ∀ (C : Type v) [TopologicalSpace C] (K : SpacetimeInterval),
    CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C ≃
      CompatibleSpacetimeEmbedding P.realization.spacetime
        (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C
  embedding_forward : ∀ (C : Type v) [TopologicalSpace C] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding R.spacetime (R.timeIntervals.interval K) C)
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a K)).Point) (x : C),
    (embeddingEquiv C K e).toSpacetime (s, x) =
      e.toSpacetime ((P.intervalTransport.diffeomorph K).symm s, x)
  embedding_inverse : ∀ (C : Type v) [TopologicalSpace C] (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding P.realization.spacetime
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C)
    (t : (R.timeIntervals.interval K).Point) (x : C),
    ((embeddingEquiv C K).symm e).toSpacetime (t, x) =
      e.toSpacetime (P.intervalTransport.diffeomorph K t, x)
  cylinderEquiv : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval),
    CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C ≃
      CompatibleSpacetimeCylinder P.realization.spacetime
        (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C
  cylinder_forward : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C)
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a K)).Point) (x : C),
    (cylinderEquiv C K e).toSpacetime (s, x) =
      e.toSpacetime ((P.intervalTransport.diffeomorph K).symm s, x)
  cylinder_inverse : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder P.realization.spacetime
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C)
    (t : (R.timeIntervals.interval K).Point) (x : C),
    ((cylinderEquiv C K).symm e).toSpacetime (t, x) =
      e.toSpacetime (P.intervalTransport.diffeomorph K t, x)
  cylinder_embedding : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C),
    (cylinderEquiv C K e).toCompatibleSpacetimeEmbedding =
      embeddingEquiv C K e.toCompatibleSpacetimeEmbedding

/-- Actual ball and based-neighborhood comparison, for one base point and
one supplied time interval. Neither a closed nor a half-open domain is
silently added; their exact correspondences are retained as separate fields. -/
structure ParabolicBallNeighborhoodTransport (P : ParabolicSpacetimeRescaling R Q hQ a)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ) (K : SpacetimeInterval) where
  ballHomeomorph : ((R.slices t).metricOnPoints.ball p r) ≃ₜ
    ((P.realization.slices (parabolicTime Q a t)).metricOnPoints.ball
      (P.sliceIdentification t p) (Real.sqrt Q * r))
  ball_forward : ∀ x, (ballHomeomorph x).val = P.sliceIdentification t x.val
  ball_inverse : ∀ x, (ballHomeomorph.symm x).val = (P.sliceIdentification t).symm x.val
  source_inclusion : ∀ x, (ballHomeomorph x).val.val = x.val.val
  neighborhoodEquiv :
    BasedBallSpacetimeNeighborhood R.spacetime R.slices R.timeIntervals t p r K ≃
      BasedBallSpacetimeNeighborhood P.realization.spacetime P.realization.slices
        R.timeIntervals (parabolicTime Q a t) (P.sliceIdentification t p)
        (Real.sqrt Q * r) (parabolicInterval Q hQ a K)
  neighborhood_forward : ∀ e
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a K)).Point) x,
    (neighborhoodEquiv e).embedding.toSpacetime (s, ballHomeomorph x) =
      e.embedding.toSpacetime ((P.intervalTransport.diffeomorph K).symm s, x)
  neighborhood_inverse : ∀ e (v : (R.timeIntervals.interval K).Point) x,
    (neighborhoodEquiv.symm e).embedding.toSpacetime (v, ballHomeomorph.symm x) =
      e.embedding.toSpacetime (P.intervalTransport.diffeomorph K v, x)
  image_eq : ∀ e,
    Set.range (neighborhoodEquiv e).embedding.toSpacetime = Set.range e.embedding.toSpacetime
  closed_time_iff : ∀ b c : ℝ,
    (parabolicInterval Q hQ a K).domain =
        Set.Icc (parabolicTime Q a b) (parabolicTime Q a c) ↔
      K.domain = Set.Icc b c
  backward_parabolic_time_iff :
    (parabolicInterval Q hQ a K).domain =
        Set.Ioc (parabolicTime Q a t - (Real.sqrt Q * r) ^ 2) (parabolicTime Q a t) ↔
      K.domain = Set.Ioc (t - r ^ 2) t

end PoincareMT
