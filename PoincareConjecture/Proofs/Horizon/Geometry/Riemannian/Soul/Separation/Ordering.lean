import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Separation.Surrounding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.EscapeCarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ordering











noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}




theorem PointSoulData.exists_arbitrarily_small_outer_neck_regions
    (P : PointSoulData g) (D : LeviCivitaData g) (hc : MetricComplete g)
    (N₁ : EpsilonNeck g) (hN₁ : N₁.epsilon ≤ neckSeparationThreshold)
    (hsmall : ¬ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ N : EpsilonNeck g, N.epsilon = N₁.epsilon → ρ ≤ N.scale) :
    ∃ A₁ B₁ : Set M,
      IsOpen A₁ ∧ IsOpen B₁ ∧ IsConnected A₁ ∧ IsConnected B₁ ∧
      Disjoint A₁ B₁ ∧ A₁ ∪ B₁ = N₁.central_sphereᶜ ∧
      frontier A₁ = N₁.central_sphere ∧ frontier B₁ = N₁.central_sphere ∧
      IsCompact (closure A₁) ∧ P.center ∈ A₁ ∧
      ¬Bornology.IsBounded (P.euclidean.symm.toHomeomorph '' B₁) ∧
      ((N₁.region (-N₁.epsilon⁻¹) 0 ⊆ A₁ ∧ N₁.region 0 N₁.epsilon⁻¹ ⊆ B₁) ∨
        (N₁.region (-N₁.epsilon⁻¹) 0 ⊆ B₁ ∧ N₁.region 0 N₁.epsilon⁻¹ ⊆ A₁)) ∧
      ∀ δ : ℝ, 0 < δ → ∃ (N₂ : EpsilonNeck g) (A₂ B₂ : Set M),
        N₂.epsilon = N₁.epsilon ∧ N₂.scale < δ ∧
        Disjoint N₂.carrier (closure N₁.carrier ∪ closure A₁) ∧
        IsOpen A₂ ∧ IsOpen B₂ ∧ IsConnected A₂ ∧ IsConnected B₂ ∧
        Disjoint A₂ B₂ ∧ A₂ ∪ B₂ = N₂.central_sphereᶜ ∧
        frontier A₂ = N₂.central_sphere ∧ frontier B₂ = N₂.central_sphere ∧
        IsCompact (closure A₂) ∧ P.center ∈ A₂ ∧
        ¬Bornology.IsBounded (P.euclidean.symm.toHomeomorph '' B₂) ∧
        ((N₂.region (-N₂.epsilon⁻¹) 0 ⊆ A₂ ∧ N₂.region 0 N₂.epsilon⁻¹ ⊆ B₂) ∨
          (N₂.region (-N₂.epsilon⁻¹) 0 ⊆ B₂ ∧ N₂.region 0 N₂.epsilon⁻¹ ⊆ A₂)) ∧
        Disjoint N₁.carrier N₂.carrier ∧ closure A₁ ⊆ A₂ ∧
        N₁.carrier ⊆ A₂ ∧ Disjoint A₁ N₂.carrier ∧ A₁ ⊆ A₂ := by
  obtain ⟨A₁, B₁, hA₁, hB₁, hA₁c, hB₁c, hdisj₁, hcover₁, hfA₁, hfB₁,
      hcompact₁, hp₁, hBu₁, hhalf₁⟩ := P.exists_surrounding_neck_regions hc N₁ hN₁
  refine ⟨A₁, B₁, hA₁, hB₁, hA₁c, hB₁c, hdisj₁, hcover₁, hfA₁, hfB₁,
    hcompact₁, hp₁, hBu₁, hhalf₁, ?_⟩
  intro δ hδ
  obtain ⟨N₂, hε₂, hscale₂, hescape⟩ :=
    EpsilonNeck.exists_small_neck_disjoint_compact_of_no_scale_lower_bound
      D N₁.epsilon hsmall ((N₁.isCompact_closure_carrier hc).union hcompact₁) hδ
  have hN₂ : N₂.epsilon ≤ neckSeparationThreshold := hε₂ ▸ hN₁
  obtain ⟨A₂, B₂, hA₂, hB₂, hA₂c, hB₂c, hdisj₂, hcover₂, hfA₂, hfB₂,
      hcompact₂, hp₂, hBu₂, hhalf₂⟩ := P.exists_surrounding_neck_regions hc N₂ hN₂
  have hescape' := disjoint_union_right.mp hescape
  have hnecks : Disjoint N₁.carrier N₂.carrier :=
    (hescape'.1.mono_right subset_closure).symm
  have hAb₁ : Bornology.IsBounded (P.euclidean.symm.toHomeomorph '' A₁) :=
    (hcompact₁.image P.euclidean.symm.toHomeomorph.continuous).isBounded.subset
      (image_mono subset_closure)
  have hAb₂ : Bornology.IsBounded (P.euclidean.symm.toHomeomorph '' A₂) :=
    (hcompact₂.image P.euclidean.symm.toHomeomorph.continuous).isBounded.subset
      (image_mono subset_closure)
  have hnest : closure A₁ ⊆ A₂ := by
    have hnested := Poincare.Topology.closures_nested_of_common_point
      P.euclidean.symm.toHomeomorph N₁.isConnected_central_sphere
      N₂.isConnected_central_sphere hA₁c.isPreconnected hA₁ hB₁ hA₂ hB₂
      hB₁c.isPreconnected hB₂c.isPreconnected hdisj₁ hdisj₂ hcover₁ hcover₂
      hfA₁ hfB₁ hfB₂ hAb₁ hAb₂ hBu₁ hBu₂
      (hnecks.mono N₁.central_sphere_subset N₂.central_sphere_subset)
      ⟨P.center, hp₁, hp₂⟩
    rcases hnested with hforward | hreverse
    · exact hforward
    · have hcenter₂ : N₂.center ∈ closure A₂ :=
        frontier_subset_closure (hfA₂.symm ▸ N₂.center_on_central_sphere)
      exact False.elim (Set.disjoint_left.mp hescape'.2
        (N₂.central_sphere_subset N₂.center_on_central_sphere)
        (subset_closure (hreverse hcenter₂)))
  obtain ⟨hcarrier, hinner_disjoint, hinner_subset⟩ :=
    N₁.carrier_ordering_of_closure_subset N₂ hA₁ hB₁ hA₂ hB₂ hdisj₁ hdisj₂
      hcover₁ hcover₂ hfA₁ hnecks hnest
  exact ⟨N₂, A₂, B₂, hε₂, hscale₂, hescape, hA₂, hB₂, hA₂c, hB₂c, hdisj₂,
    hcover₂, hfA₂, hfB₂, hcompact₂, hp₂, hBu₂, hhalf₂, hnecks, hnest,
    hcarrier, hinner_disjoint, hinner_subset⟩

end PoincareConjecture.RiemannianMetric
