import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.Components
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected

/-!
# Exhaustive ambient sides of a separating neck

The two local halves determine all complementary components in the ambient
component of the neck center. Their common frontier is the actual central
sphere, so no further complementary component can occur away from the collar.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.DeepHorn

theorem frontier_component_compl_subset
    {M : Type*} [TopologicalSpace M] [LocallyConnectedSpace M]
    {S : Set M} (hS : IsClosed S) {p : M} (hp : p ∈ Sᶜ) :
    frontier (connectedComponentIn Sᶜ p) ⊆ S := by
  intro x hx
  by_contra hxS
  have hmem : (⟨x, hxS⟩ : ↥(Sᶜ)) ∈ connectedComponent (⟨p, hp⟩ : ↥(Sᶜ)) := by
    rw [← (isClosed_connectedComponent (x := (⟨p, hp⟩ : ↥(Sᶜ)))).closure_eq]
    apply closure_subtype.mpr
    rw [← connectedComponentIn_eq_image hp]
    exact hx.1
  have hxC : x ∈ connectedComponentIn Sᶜ p := by
    rw [connectedComponentIn_eq_image hp]
    exact ⟨⟨x, hxS⟩, hmem, rfl⟩
  exact hx.2 ((hS.isOpen_compl.connectedComponentIn).interior_eq.symm ▸ hxC)

end PoincareMT.DeepHorn

namespace PoincareMT.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

/-- Separation gives exactly two open connected sides in the component
of the center, with the entire central sphere as each side's frontier. -/
theorem exists_exhaustive_complementary_regions (N : EpsilonNeck g)
    (hN : N.IsSeparating) :
    ∃ A B : Set M, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = connectedComponent N.center \ N.central_sphere ∧
      frontier A = N.central_sphere ∧ frontier B = N.central_sphere ∧
      frontier (closure A) = N.central_sphere ∧ frontier (closure B) = N.central_sphere ∧
      (interior (closure A)).Nonempty ∧ (interior (closure B)).Nonempty := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  have hi := inv_pos.mpr N.epsilon_pos
  obtain ⟨p, hp⟩ := (N.isConnected_region le_rfl hi.le (neg_lt_zero.mpr hi)).nonempty
  obtain ⟨q, hq⟩ := (N.isConnected_region (neg_nonpos.mpr hi.le) le_rfl hi).nonempty
  let A := connectedComponentIn N.central_sphereᶜ p
  let B := connectedComponentIn N.central_sphereᶜ q
  obtain ⟨hAo, hBo, hAc, hBc, hdis, hneg, hpos, hfA, hfB, hiA, hiB⟩ :=
    N.complementary_component_frontiers hN hp hq
  have hpS : p ∈ N.central_sphereᶜ := (connectedComponentIn_subset _ _ (hneg hp))
  have hqS : q ∈ N.central_sphereᶜ := (connectedComponentIn_subset _ _ (hpos hq))
  have hfrontA : frontier A = N.central_sphere :=
    Subset.antisymm (DeepHorn.frontier_component_compl_subset N.isClosed_central_sphere hpS)
      (hfA ▸ frontier_closure_subset)
  have hfrontB : frontier B = N.central_sphere :=
    Subset.antisymm (DeepHorn.frontier_component_compl_subset N.isClosed_central_sphere hqS)
      (hfB ▸ frontier_closure_subset)
  have hclA : closure A = A ∪ N.central_sphere := by
    rw [closure_eq_self_union_frontier, hfrontA]
  have hclB : closure B = B ∪ N.central_sphere := by
    rw [closure_eq_self_union_frontier, hfrontB]
  have hcarrier : N.carrier ⊆ A ∪ N.central_sphere ∪ B := by
    intro x hx
    rcases N.carrier_subset_region_union_central_union_region hx with (hn | hs) | hp
    · exact Or.inl (Or.inl (hneg hn))
    · exact Or.inl (Or.inr hs)
    · exact Or.inr (hpos hp)
  have hUeq : closure A ∪ closure B = A ∪ N.carrier ∪ B := by
    rw [hclA, hclB]
    apply Subset.antisymm
    · intro x hx
      rcases hx with (ha | hs) | (hb | hs)
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr (N.central_sphere_subset hs))
      · exact Or.inr hb
      · exact Or.inl (Or.inr (N.central_sphere_subset hs))
    · intro x hx
      rcases hx with (ha | hn) | hb
      · exact Or.inl (Or.inl ha)
      · rcases hcarrier hn with (ha | hs) | hb
        · exact Or.inl (Or.inl ha)
        · exact Or.inl (Or.inr hs)
        · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inl hb)
  have hUo : IsOpen (closure A ∪ closure B) := by
    rw [hUeq]
    exact (hAo.union N.carrier_open).union hBo
  have hCU : connectedComponent N.center ⊆ closure A ∪ closure B :=
    (show IsClopen (closure A ∪ closure B) from
      ⟨isClosed_closure.union isClosed_closure, hUo⟩).connectedComponent_subset
        (by rw [hclA]; exact Or.inl (Or.inr N.center_on_central_sphere))
  have hAC : A ⊆ connectedComponent N.center := by
    rw [connectedComponent_eq (N.carrier_subset_connectedComponent hp.1)]
    exact hAc.isPreconnected.subset_connectedComponent (hneg hp)
  have hBC : B ⊆ connectedComponent N.center := by
    rw [connectedComponent_eq (N.carrier_subset_connectedComponent hq.1)]
    exact hBc.isPreconnected.subset_connectedComponent (hpos hq)
  refine ⟨A, B, hAo, hBo, hAc, hBc, hdis, ?_, hfrontA, hfrontB, hfA, hfB, hiA, hiB⟩
  apply Subset.antisymm
  · intro x hx
    rcases hx with ha | hb
    · exact ⟨hAC ha, connectedComponentIn_subset _ _ ha⟩
    · exact ⟨hBC hb, connectedComponentIn_subset _ _ hb⟩
  · intro x hx
    have hh := hCU hx.1
    rw [hclA, hclB] at hh
    rcases hh with (ha | hs) | (hb | hs)
    · exact Or.inl ha
    · exact False.elim (hx.2 hs)
    · exact Or.inr hb
    · exact False.elim (hx.2 hs)

end PoincareMT.EpsilonNeck
