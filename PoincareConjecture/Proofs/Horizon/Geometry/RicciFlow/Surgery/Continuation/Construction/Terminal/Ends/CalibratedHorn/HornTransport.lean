import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.CenterTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.HornNecks

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T} (horn : StrongHorn E epsilon)

theorem boundary_sphere_smooth_transport_of_epsilon_le (hε : epsilon ≤ 1 / 200)
    (N : EpsilonNeck (E.extended.metric T)) (hN : N.epsilon ≤ 1 / 200)
    (hcenter : N.center ∈ horn.carrier) :
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) (E.extended.slice T).carrier
        (E.extended.slice T).carrier ∞) (K : Set (E.extended.slice T).carrier),
      IsCompact K ∧ (∀ x, x ∉ K → D x = x) ∧
        D '' horn.boundary_sphere = N.central_sphere ∧ N.IsSeparating := by
  have hhalf : epsilon < 1 / 2 := hε.trans_lt (by norm_num)
  obtain ⟨N₀, hN₀⟩ := horn.boundary_neck
  let P := N₀.spatialNeck hhalf
  have hp : P.center ∈ horn.carrier :=
    horn.boundary_sphere_subset_carrier (hN₀ ▸ P.center_on_central_sphere)
  have hcover : ∀ x ∈ horn.carrier,
      ∃ Q : EpsilonNeck (E.extended.metric T), Q.epsilon ≤ 1 / 200 ∧ Q.center = x := by
    intro x hx
    obtain ⟨Q, hQ⟩ := horn.every_point_neck x hx
    exact ⟨Q.spatialNeck hhalf, hε, hQ⟩
  obtain ⟨D, K, hK, hfix, hsphere⟩ :=
    EpsilonNeck.connected_center_smooth_transport_of_epsilon_le horn.carrier
      horn.isPreconnected_carrier hcover P N hε hN hp hcenter
  have hcomponent : D '' connectedComponent P.center = connectedComponent N.center := by
    have h := D.toHomeomorph.image_connectedComponentIn (s := univ) (x := P.center) (mem_univ _)
    simp only [connectedComponentIn_univ, image_univ, D.toHomeomorph.surjective.range_eq] at h
    apply h.trans
    symm
    apply connectedComponent_eq
    apply N.carrier_subset_connectedComponent
    apply N.central_sphere_subset
    rw [← hsphere]
    exact mem_image_of_mem D P.center_on_central_sphere
  have hsep : N.IsSeparating :=
    (P.isSeparating_iff_of_homeomorph N D.toHomeomorph hcomponent hsphere).mp
      (horn.boundary_neck_isSeparating N₀ hhalf hN₀)
  refine ⟨D, K, hK, hfix, ?_, hsep⟩
  change D '' N₀.central_sphere = N.central_sphere at hsphere
  rwa [hN₀] at hsphere

theorem nonempty_neckCap_tube_of_epsilon_le
    (A : RepairedNeckCapTopologyTheory.{u}) (hεpos : 0 < epsilon)
    (hA : epsilon ≤ A.epsilon₀) :
    Nonempty (CorrectedA19Conclusion (E.extended.metric T)
      (horn.neckOnlyCover A hεpos hA)) := by
  have hε : epsilon ≤ 1 / 200 := hA.trans A.epsilon₀_le_one_two_hundred
  apply A.a19 (E.extended.metric T) (horn.neckOnlyCover A hεpos hA) hA
  intro N hN
  obtain ⟨_, _, _, _, _, hsep⟩ :=
    horn.boundary_sphere_smooth_transport_of_epsilon_le hε N (hN.1.trans_le hε) hN.2
  exact hsep

end PoincareConjecture.StrongHorn
