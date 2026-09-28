import PoincareConjecture.Proofs.M13.DomainMaps
import PoincareConjecture.Proofs.M13.Time

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M13

theorem spacetimeInterval_ext {I J : SpacetimeInterval} (h : I.domain = J.domain) :
    I = J := by
  cases I
  cases J
  cases h
  rfl

noncomputable def inverseParabolicInterval (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) : SpacetimeInterval where
  domain := parabolicTimeInv Q a '' I.domain
  ordConnected := by
    let : I.domain.OrdConnected := I.ordConnected
    exact Set.ordConnected_image (parabolicTimeOrderIso Q hQ a).symm
  nontrivial := I.nontrivial.image (parabolicTimeOrderIso Q hQ a).symm.injective

theorem parabolicInterval_inverseParabolicInterval (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) :
    parabolicInterval Q hQ a (inverseParabolicInterval Q hQ a I) = I := by
  apply spacetimeInterval_ext
  change parabolicTime Q a '' (parabolicTimeInv Q a '' I.domain) = I.domain
  ext t
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hst⟩
    rw [parabolicTime_parabolicTimeInv Q hQ a] at hst
    exact hst ▸ hs
  · intro ht
    exact ⟨parabolicTimeInv Q a t, ⟨t, ht, rfl⟩,
      parabolicTime_parabolicTimeInv Q hQ a t⟩

theorem parabolicInterval_surjective (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    Function.Surjective (parabolicInterval Q hQ a) := by
  intro I
  exact ⟨inverseParabolicInterval Q hQ a I,
    parabolicInterval_inverseParabolicInterval Q hQ a I⟩

theorem parabolicInterval_family_surjective (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    {B : Type u} (J : B → SpacetimeInterval) :
    ∃ K : B → SpacetimeInterval, (fun b ↦ parabolicInterval Q hQ a (K b)) = J := by
  exact ⟨fun b ↦ inverseParabolicInterval Q hQ a (J b),
    funext (fun b ↦ parabolicInterval_inverseParabolicInterval Q hQ a (J b))⟩

theorem affineInterval_forward_inverse_point (T : SpacetimeIntervalSystem)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (K : SpacetimeInterval)
    (s : ℝ) (hs : s ∈ (parabolicInterval Q hQ a K).domain) :
    (parabolicIntervalTransport T Q hQ a).diffeomorph K
      ⟨parabolicTimeInv Q a s, (mem_parabolicInterval_iff Q hQ a K s).1 hs⟩ = ⟨s, hs⟩ := by
  apply Subtype.ext
  exact parabolicTime_parabolicTimeInv Q hQ a s

theorem affineInterval_inverse_forward_point (T : SpacetimeIntervalSystem)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (K : SpacetimeInterval)
    (t : ℝ) (ht : t ∈ K.domain) :
    ((parabolicIntervalTransport T Q hQ a).diffeomorph K).symm
      ⟨parabolicTime Q a t,
        (parabolicTime_mem_parabolicInterval_iff Q hQ a K t).2 ht⟩ = ⟨t, ht⟩ := by
  apply Subtype.ext
  exact parabolicTimeInv_parabolicTime Q hQ a t

theorem affineInterval_inverse_inclusion (T : SpacetimeIntervalSystem)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain)
    (h' : (parabolicInterval Q hQ a L).domain ⊆ (parabolicInterval Q hQ a K).domain)
    (s : (T.interval (parabolicInterval Q hQ a L)).Point) :
    ((parabolicIntervalTransport T Q hQ a).diffeomorph K).symm
      (spacetimeIntervalInclusion _ _ h' s) =
        spacetimeIntervalInclusion _ _ h
          (((parabolicIntervalTransport T Q hQ a).diffeomorph L).symm s) := rfl

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem untransportedWorldline_point (K : SpacetimeInterval)
    (e : SpacetimeWorldline (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)))
    (s : ℝ) (hs : s ∈ (parabolicInterval Q hQ a K).domain) :
    (untransportedWorldline K e).curve
      ⟨parabolicTimeInv Q a s, (mem_parabolicInterval_iff Q hQ a K s).1 hs⟩ =
        e.curve ⟨s, hs⟩ := by
  change e.curve ((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K _) = _
  rw [affineInterval_forward_inverse_point]

theorem untransportedEmbedding_point {C : Type v} [TopologicalSpace C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C)
    (s : ℝ) (hs : s ∈ (parabolicInterval Q hQ a K).domain) (x : C) :
    (untransportedEmbedding K e).toSpacetime
      (⟨parabolicTimeInv Q a s, (mem_parabolicInterval_iff Q hQ a K s).1 hs⟩, x) =
        e.toSpacetime (⟨s, hs⟩, x) := by
  change e.toSpacetime
    ((parabolicIntervalTransport R.timeIntervals Q hQ a).diffeomorph K _, x) = _
  rw [affineInterval_forward_inverse_point]

theorem untransportedCylinder_point {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C)
    (s : ℝ) (hs : s ∈ (parabolicInterval Q hQ a K).domain) (x : C) :
    (untransportedCylinder K e).toSpacetime
      (⟨parabolicTimeInv Q a s, (mem_parabolicInterval_iff Q hQ a K s).1 hs⟩, x) =
        e.toSpacetime (⟨s, hs⟩, x) :=
  untransportedEmbedding_point K e.toCompatibleSpacetimeEmbedding s hs x

end PoincareConjecture.M13
