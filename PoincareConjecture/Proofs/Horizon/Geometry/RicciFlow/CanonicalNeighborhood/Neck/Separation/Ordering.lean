import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ambient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected

set_option autoImplicit false

open Set

namespace Poincare.Topology

theorem closure_subset_of_separator_subset
    {M : Type*} [TopologicalSpace M]
    (h : M ≃ₜ EuclideanSpace ℝ (Fin 3))
    {S₁ A₁ B₁ S₂ A₂ B₂ : Set M}
    (hA₁ : IsOpen A₁) (hB₁ : IsOpen B₁) (hB₂c : IsPreconnected B₂)
    (hdisj₁ : Disjoint A₁ B₁) (hdisj₂ : Disjoint A₂ B₂)
    (hcover₁ : A₁ ∪ B₁ = S₁ᶜ) (hcover₂ : A₂ ∪ B₂ = S₂ᶜ)
    (hfB₁ : frontier B₁ = S₁) (hfB₂ : frontier B₂ = S₂)
    (hAb : Bornology.IsBounded (h '' A₁))
    (hBu : ¬ Bornology.IsBounded (h '' B₂)) (hS : S₁ ⊆ A₂) :
    closure A₁ ⊆ A₂ := by
  have hB₂cover : B₂ ⊆ A₁ ∪ B₁ := by
    intro x hx
    rw [hcover₁]
    exact fun hxS => Set.disjoint_left.mp hdisj₂ (hS hxS) hx
  have hB₂B₁ : B₂ ⊆ B₁ := by
    rcases hB₂c.subset_or_subset hA₁ hB₁ hdisj₁ hB₂cover with hleft | hright
    · exact False.elim (hBu (hAb.subset (image_mono hleft)))
    · exact hright
  have hclosedDisj := hdisj₁.closure_left hB₁
  intro x hx
  by_contra hxA₂
  have hxclB₂ : x ∈ closure B₂ := by
    rw [closure_eq_self_union_frontier, hfB₂]
    by_cases hxS₂ : x ∈ S₂
    · exact Or.inr hxS₂
    · have hxcover : x ∈ A₂ ∪ B₂ := by rwa [hcover₂]
      exact Or.inl (hxcover.resolve_left hxA₂)
  have hxclB₁ := closure_mono hB₂B₁ hxclB₂
  rw [closure_eq_self_union_frontier, hfB₁] at hxclB₁
  rcases hxclB₁ with hxB₁ | hxS₁
  · exact Set.disjoint_left.mp hclosedDisj hx hxB₁
  · exact hxA₂ (hS hxS₁)

theorem closures_nested_of_common_point
    {M : Type*} [TopologicalSpace M]
    (h : M ≃ₜ EuclideanSpace ℝ (Fin 3))
    {S₁ A₁ B₁ S₂ A₂ B₂ : Set M}
    (hS₁ : IsConnected S₁) (hS₂ : IsConnected S₂)
    (hA₁c : IsPreconnected A₁)
    (hA₁ : IsOpen A₁) (hB₁ : IsOpen B₁)
    (hA₂ : IsOpen A₂) (hB₂ : IsOpen B₂)
    (hB₁c : IsPreconnected B₁) (hB₂c : IsPreconnected B₂)
    (hdisj₁ : Disjoint A₁ B₁) (hdisj₂ : Disjoint A₂ B₂)
    (hcover₁ : A₁ ∪ B₁ = S₁ᶜ) (hcover₂ : A₂ ∪ B₂ = S₂ᶜ)
    (hfA₁ : frontier A₁ = S₁)
    (hfB₁ : frontier B₁ = S₁) (hfB₂ : frontier B₂ = S₂)
    (hA₁b : Bornology.IsBounded (h '' A₁))
    (hA₂b : Bornology.IsBounded (h '' A₂))
    (hB₁u : ¬ Bornology.IsBounded (h '' B₁))
    (hB₂u : ¬ Bornology.IsBounded (h '' B₂))
    (hSdisj : Disjoint S₁ S₂) (hcommon : (A₁ ∩ A₂).Nonempty) :
    closure A₁ ⊆ A₂ ∨ closure A₂ ⊆ A₁ := by
  have hS₁cover : S₁ ⊆ A₂ ∪ B₂ := by
    rw [hcover₂]
    exact hSdisj.subset_compl_right
  rcases hS₁.isPreconnected.subset_or_subset hA₂ hB₂ hdisj₂ hS₁cover with hleft | hright
  · exact Or.inl (closure_subset_of_separator_subset h hA₁ hB₁ hB₂c
      hdisj₁ hdisj₂ hcover₁ hcover₂ hfB₁ hfB₂ hA₁b hB₂u hleft)
  have hS₂cover : S₂ ⊆ A₁ ∪ B₁ := by
    rw [hcover₁]
    exact hSdisj.symm.subset_compl_right
  rcases hS₂.isPreconnected.subset_or_subset hA₁ hB₁ hdisj₁ hS₂cover with hleft | hright₂
  · exact Or.inr (closure_subset_of_separator_subset h hA₂ hB₂ hB₁c
      hdisj₂ hdisj₁ hcover₂ hcover₁ hfB₂ hfB₁ hA₂b hB₁u hleft)
  have hA₁cover : A₁ ⊆ A₂ ∪ B₂ := by
    intro x hx
    rw [hcover₂]
    exact fun hxS => Set.disjoint_left.mp hdisj₁ hx (hright₂ hxS)
  rcases hA₁c.subset_or_subset hA₂ hB₂ hdisj₂ hA₁cover with hinside | houtside
  · obtain ⟨x, hx⟩ := hS₁.nonempty
    have hxcl : x ∈ closure A₁ := frontier_subset_closure (hfA₁.symm ▸ hx)
    exact False.elim (Set.disjoint_left.mp (hdisj₂.closure_left hB₂)
      (closure_mono hinside hxcl) (hright hx))
  · obtain ⟨x, hx₁, hx₂⟩ := hcommon
    exact False.elim (Set.disjoint_left.mp hdisj₂ hx₂ (houtside hx₁))

end Poincare.Topology

open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem carrier_ordering_of_closure_subset
    (N₁ N₂ : EpsilonNeck g) {A₁ B₁ A₂ B₂ : Set M}
    (hA₁ : IsOpen A₁) (hB₁ : IsOpen B₁)
    (hA₂ : IsOpen A₂) (hB₂ : IsOpen B₂)
    (hdisj₁ : Disjoint A₁ B₁) (hdisj₂ : Disjoint A₂ B₂)
    (hcover₁ : A₁ ∪ B₁ = N₁.central_sphereᶜ)
    (hcover₂ : A₂ ∪ B₂ = N₂.central_sphereᶜ)
    (hfA₁ : frontier A₁ = N₁.central_sphere)
    (hneck : Disjoint N₁.carrier N₂.carrier)
    (hnest : closure A₁ ⊆ A₂) :
    N₁.carrier ⊆ A₂ ∧ Disjoint A₁ N₂.carrier ∧ A₁ ⊆ A₂ := by
  have hA₁A₂ : A₁ ⊆ A₂ := subset_closure.trans hnest
  have hcenter₁ : N₁.center ∈ A₂ := hnest
    (frontier_subset_closure (hfA₁.symm ▸ N₁.center_on_central_sphere))
  have hN₁cover : N₁.carrier ⊆ A₂ ∪ B₂ := by
    rw [hcover₂]
    exact (hneck.mono_right N₂.central_sphere_subset).subset_compl_right
  have hN₁A₂ : N₁.carrier ⊆ A₂ := by
    rcases N₁.isConnected_carrier.isPreconnected.subset_or_subset
      hA₂ hB₂ hdisj₂ hN₁cover with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp hdisj₂ hcenter₁
        (h (N₁.central_sphere_subset N₁.center_on_central_sphere)))
  have hN₂cover : N₂.carrier ⊆ A₁ ∪ B₁ := by
    rw [hcover₁]
    exact (hneck.symm.mono_right N₁.central_sphere_subset).subset_compl_right
  have hN₂B₁ : N₂.carrier ⊆ B₁ := by
    rcases N₂.isConnected_carrier.isPreconnected.subset_or_subset
      hA₁ hB₁ hdisj₁ hN₂cover with h | h
    · have hc : N₂.center ∈ A₂ ∪ B₂ := Or.inl (hA₁A₂
        (h (N₂.central_sphere_subset N₂.center_on_central_sphere)))
      rw [hcover₂] at hc
      exact False.elim (hc N₂.center_on_central_sphere)
    · exact h
  exact ⟨hN₁A₂, hdisj₁.mono_right hN₂B₁, hA₁A₂⟩

end PoincareConjecture.EpsilonNeck
