import PoincareConjecture.Proofs.M38.CapExclusion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem compact_component_neck_cap_models (x : M)
    (hx : IsCompact (connectedComponent x))
    (R : NeckCapRegion g (connectedComponent x)) :
    (∃ kind, Nonempty (ClosedComponentCertificate kind (connectedComponent x))) ∨
      ∃ Q : SphereBundleCircleCertificate g (connectedComponent x),
        Q.carrier = connectedComponent x := by
  cases R with
  | twoCaps kind cap₁ cap₂ C _ hcontains =>
    have heq := Set.Subset.antisymm
      (C.connected.subset_connectedComponent (hcontains mem_connectedComponent)) hcontains
    exact Or.inl ⟨kind, ⟨heq ▸ C⟩⟩
  | doubleCappedTube certificate kind C hcontains =>
    have heq := Set.Subset.antisymm
      (C.connected.subset_connectedComponent (hcontains mem_connectedComponent)) hcontains
    exact Or.inl ⟨kind, ⟨heq ▸ C⟩⟩
  | singleCap C hcontains =>
    exact (no_cap_containing_compact_component x hx C hcontains).elim
  | cappedTube C hcontains =>
    exact (no_capped_tube_model_containing_compact_component x hx C hcontains).elim
  | tube C =>
    exact ((no_tube_containing_compact_component x hx).false C).elim
  | fibration Q =>
    exact Or.inr ⟨Q, Set.Subset.antisymm
      (Q.connected.subset_connectedComponent (Q.contains_X mem_connectedComponent))
      Q.contains_X⟩

theorem whole_canonical_component_models
    (N : RepairedNeckCapTopologyTheory.{u}) (F : SurgeryFlowData.{u}) (t : ℝ)
    (x : (F.slice t).carrier) (hx : IsCompact (connectedComponent x))
    (hcontrol : ∀ y ∈ connectedComponent x,
      SurgeryCanonicalControl F t y F.parameters.epsilon F.parameters.C)
    (hepsilon : F.parameters.epsilon ≤ N.epsilon₀) :
    (∃ kind, Nonempty (ClosedComponentCertificate kind (connectedComponent x))) ∨
    (∃ Q : SphereBundleCircleCertificate (F.metric t) (connectedComponent x),
      Q.carrier = connectedComponent x) ∨
    (∃ Q : SingularRoundComponent (F.metric t) F.parameters.epsilon,
      Q.carrier = connectedComponent x) := by
  rcases canonical_region N F t isConnected_connectedComponent hcontrol hepsilon with
    ⟨H, hX, _, _, _, ⟨D⟩⟩ | ⟨Q, hcontains⟩ | ⟨Q, hcontains⟩
  · rcases compact_component_neck_cap_models x hx (hX ▸ D.region) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hconnected : IsConnected Q.carrier := by
      rw [Q.component_eq]
      exact isConnected_connectedComponent
    have heq := Set.Subset.antisymm
      (hconnected.subset_connectedComponent (hcontains mem_connectedComponent)) hcontains
    rcases Q.topology with C | C
    · exact Or.inl ⟨.threeSphere, heq ▸ C⟩
    · exact Or.inl ⟨.realProjectiveThree, heq ▸ C⟩
  · have hconnected : IsConnected Q.carrier := by
      rw [Q.component_eq]
      exact isConnected_connectedComponent
    exact Or.inr (Or.inr ⟨Q, Set.Subset.antisymm
      (hconnected.subset_connectedComponent (hcontains mem_connectedComponent)) hcontains⟩)

end PoincareConjecture.M38
