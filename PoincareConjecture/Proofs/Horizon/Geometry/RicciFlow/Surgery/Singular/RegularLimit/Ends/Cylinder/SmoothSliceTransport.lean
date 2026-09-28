import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.SmoothGraphTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.SliceIsotopy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Manifold Topology

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_contained_slice_smooth_transport :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (N P : EpsilonNeck g),
        N.epsilon ≤ ε₀ → P.epsilon ≤ ε₀ →
        ∀ {a : ℝ}, a ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ →
        (∀ q : UnitTwoSphere, P.coordinate_map (q, a) ∈ N.carrier) →
          ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M),
            IsCompact K ∧ K ⊆ N.carrier ∪ P.carrier ∧
            (∀ x, x ∉ K → D x = x) ∧
            D '' P.central_sphere = N.central_sphere := by
  obtain ⟨ε₀, hε₀, hsmall, hgraph⟩ := exists_sphereSlice_graph_and_isotopy.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hN hP a ha hmem
  obtain ⟨h, hh, hdom, hslice, _⟩ := hgraph N P hN hP ha hmem
  obtain ⟨DN, KN, hKN, hKNN, hDNfix, _, hDNsphere⟩ :=
    N.exists_smooth_graph_transport h hh hdom
  obtain ⟨DP, KP, hKP, hKPP, hDPfix, _, hDPsphere⟩ :=
    P.exists_smooth_graph_transport (fun _ => a) contMDiff_const (fun _ => ha)
  refine ⟨DP.trans DN.symm, KN ∪ KP, hKN.union hKP,
    union_subset_union hKNN hKPP, ?_, ?_⟩
  · intro x hx
    change DN.symm (DP x) = x
    rw [hDPfix x (fun h => hx (Or.inr h))]
    have hfix := hDNfix x (fun h => hx (Or.inl h))
    exact (congrArg DN.symm hfix).symm.trans (DN.symm_apply_apply x)
  · change (DN.symm ∘ DP) '' P.central_sphere = N.central_sphere
    rw [image_comp, hDPsphere, hslice, ← hDNsphere]
    exact DN.toEquiv.symm_image_image _

end PoincareConjecture.EpsilonNeck
