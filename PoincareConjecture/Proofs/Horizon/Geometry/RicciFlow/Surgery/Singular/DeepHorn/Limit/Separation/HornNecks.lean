import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.SphereTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Noncompact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Theory








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StrongHorn



theorem exists_boundary_sphere_transport :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T ε : ℝ}
        (E : GeneralizedFlowExtension F T),
        0 < ε → ε ≤ ε₀ → ∀ horn : StrongHorn E ε,
        ∀ N : EpsilonNeck (E.extended.metric T), N.epsilon = ε → N.center ∈ horn.carrier →
        ∃ (e : (E.extended.slice T).carrier ≃ₜ (E.extended.slice T).carrier)
          (K : Set (E.extended.slice T).carrier), IsCompact K ∧
          (∀ x, x ∉ K → e x = x) ∧ e '' horn.boundary_sphere = N.central_sphere ∧
          N.IsSeparating := by
  obtain ⟨ε₀, hε₀, hsmall, htransport⟩ :=
    EpsilonNeck.exists_connected_center_compact_transport.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro F T ε E hεpos hε horn N hN hcenter
  have hhalf : ε < 1 / 2 := (hε.trans hsmall).trans_lt (by norm_num)
  obtain ⟨N₀, hN₀⟩ := horn.boundary_neck
  let P := N₀.spatialNeck hhalf
  have hp : P.center ∈ horn.carrier :=
    horn.boundary_sphere_subset_carrier (hN₀ ▸ P.center_on_central_sphere)
  have hcover : ∀ x ∈ horn.carrier,
      ∃ Q : EpsilonNeck (E.extended.metric T), Q.epsilon = ε ∧ Q.center = x := by
    intro x hx
    obtain ⟨Q, hQ⟩ := horn.every_point_neck x hx
    exact ⟨Q.spatialNeck hhalf, rfl, hQ⟩
  obtain ⟨e, K, hK, hfix, hsphere⟩ := htransport hεpos hε horn.carrier
    horn.isPreconnected_carrier hcover P N rfl hN hp hcenter
  have hcomponent : e '' connectedComponent P.center = connectedComponent N.center := by
    have h := e.image_connectedComponentIn (s := univ) (x := P.center) (mem_univ _)
    simp only [connectedComponentIn_univ, image_univ, e.surjective.range_eq] at h
    apply h.trans
    symm
    apply connectedComponent_eq
    apply N.carrier_subset_connectedComponent
    apply N.central_sphere_subset
    rw [← hsphere]
    exact mem_image_of_mem e P.center_on_central_sphere
  have hsep : N.IsSeparating :=
    (P.isSeparating_iff_of_homeomorph N e hcomponent hsphere).mp
      (horn.boundary_neck_isSeparating N₀ hhalf hN₀)
  refine ⟨e, K, hK, hfix, ?_, hsep⟩
  change e '' N₀.central_sphere = N.central_sphere at hsphere
  rwa [hN₀] at hsphere

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}



noncomputable def neckOnlyCover (horn : StrongHorn E epsilon)
    (A : RepairedNeckCapTopologyTheory.{u}) (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ A.epsilon₀) : NeckOnlyCover (E.extended.metric T) where
  epsilon := epsilon
  epsilon_pos := hepsilon
  epsilon_threshold := A.epsilon₀
  epsilon_threshold_pos := A.epsilon₀_pos
  epsilon_threshold_le_one_two_hundred := A.epsilon₀_le_one_two_hundred
  epsilon_le_threshold := hsmall
  X := horn.carrier
  connected_X := ⟨by
    let q : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
    exact ⟨horn.coordinate (q, ⟨0, le_rfl, by norm_num⟩), Subtype.property _⟩,
    horn.isPreconnected_carrier⟩
  necks := {N | N.epsilon = epsilon ∧ N.center ∈ horn.carrier}
  pointwise_center_cover := by
    intro x hx
    obtain ⟨N, hN⟩ := horn.every_point_neck x hx
    let hhalf : epsilon < 1 / 2 :=
      (hsmall.trans A.epsilon₀_le_one_two_hundred).trans_lt (by norm_num)
    refine ⟨N.spatialNeck hhalf, ⟨rfl, ?_⟩, hN⟩
    change N.center ∈ horn.carrier
    rw [hN]
    exact hx
  neck_epsilon := fun _ hN => hN.1



theorem exists_neckCap_tube_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T ε : ℝ}
        (E : GeneralizedFlowExtension F T),
        ∀ (A : RepairedNeckCapTopologyTheory.{u}) (hεpos : 0 < ε)
          (_hε : ε ≤ ε₀) (hA : ε ≤ A.epsilon₀) (horn : StrongHorn E ε),
        Nonempty (CorrectedA19Conclusion (E.extended.metric T)
          (horn.neckOnlyCover A hεpos hA)) := by
  obtain ⟨ε₀, hε₀, hsmall, htransport⟩ := exists_boundary_sphere_transport.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro F T ε E A hεpos hε hA horn
  apply A.a19 (E.extended.metric T) (horn.neckOnlyCover A hεpos hA) hA
  intro N hN
  obtain ⟨_, _, _, _, _, hsep⟩ := htransport E hεpos hε horn N hN.1 hN.2
  exact hsep

end PoincareConjecture.StrongHorn
