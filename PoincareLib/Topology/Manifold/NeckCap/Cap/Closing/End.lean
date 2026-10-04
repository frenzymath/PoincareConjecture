import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Transport
import PoincareLib.Topology.Manifold.NeckCap.Cap.Core.BoundaryTransport
import PoincareLib.Topology.Manifold.NeckCap.Overlap.ContainedSphere

/-!
# Closing caps along an end neck

When the second cap boundary lies in the first cap's end neck, composing
the two supported sphere transports aligns the cap boundaries. Frontier
contact of the second closed core then closes the original carriers to a
compact component.

Reference: Morgan--Tian, Claims A.23--A.24, pp. 512--513.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

/-- A boundary sphere contained in the first cap's end, together with
frontier contact, closes the two original cap carriers at a universal threshold. -/
theorem exists_end_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (C D : CapCertificate g),
        C.epsilon = ε → D.epsilon = ε →
        D.boundary_sphere ⊆ C.end_neck.carrier →
        (frontier C.carrier ∩ D.closed_core).Nonempty →
        C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
          IsCompact (C.carrier ∪ D.carrier) := by
  obtain ⟨ε₁, hε₁, hsmall, hboundary⟩ := exists_boundary_end_transport_threshold.{u}
  obtain ⟨ε₂, hε₂, _, htransport⟩ := EpsilonNeck.exists_contained_compact_transport.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε hεpos hε C D hC hD hsubset hcontact
  obtain ⟨e, K, _, hK, hfix, he⟩ := hboundary C (hC ▸ hε.trans (min_le_left _ _))
  obtain ⟨f, L, _, hL, hfixf, _, hf⟩ := htransport hεpos
    (hε.trans (min_le_right _ _)) C.end_neck D.boundary_neck
    (C.end_neck_epsilon.trans hC) (D.boundary_neck_epsilon.trans hD)
    (D.boundary_eq_neck_sphere ▸ hsubset)
  apply C.compact_component_of_boundary_transport_fixed_outside D (e.trans f) _ _ hcontact
  · change (f ∘ e) '' C.boundary_sphere = D.boundary_sphere
    rw [image_comp, he, hf, D.boundary_eq_neck_sphere]
  · intro x hx
    change f (e x) = x
    rw [hfix x (fun h => hx (hK h)), hfixf x (fun h => hx (C.end_neck_subset (hL h)))]

end PoincareMT.CapCertificate
