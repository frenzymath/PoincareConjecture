import PoincareLib.Topology.Manifold.Surgery.Event.Cap.CapExclusion

/-!
# Models for whole compact canonical components

Apply the supplied Appendix A theory to a whole compact ambient component.
Connected containment becomes equality. The noncompact tube, single-cap and
capped-tube alternatives are impossible, leaving actual closed-component,
sphere-bundle or round certificates on precisely that component.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

/-- In Appendix A's six-case output for a whole compact component, only a
closed-component certificate or a sphere-bundle certificate can remain.
This does not classify any proper subset of a containing model. -/
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

/-- Strong canonical control on a whole compact component, together with
the supplied Appendix A theory at its uniform threshold, gives an actual
closed, sphere-bundle or round model for that literal component.
Source: Proposition 15.3, pp. 357-358, wholly disappearing components. -/
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

end PoincareMT.M38
