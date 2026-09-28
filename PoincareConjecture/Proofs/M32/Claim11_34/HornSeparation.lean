import PoincareConjecture.Proofs.M32.Thm11_31.Boundary
import PoincareConjecture.Proofs.M32.Neck.ConnectedTransport
import PoincareConjecture.Proofs.M32.Claim11_34.Noncompact
import PoincareConjecture.Statements.M25NeckCapTopology














set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32




theorem exists_horn_boundary_sphere_transport :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
        (E : GeneralizedFlowExtension F T),
        0 < epsilon → epsilon ≤ epsilon₀ → ∀ horn : StrongHorn E epsilon,
        ∀ N : EpsilonNeck (E.extended.metric T),
          N.epsilon = epsilon → N.center ∈ horn.carrier →
          ∃ (e : (E.extended.slice T).carrier ≃ₜ (E.extended.slice T).carrier)
            (K : Set (E.extended.slice T).carrier), IsCompact K ∧
            (∀ x, x ∉ K → e x = x) ∧ e '' horn.boundary_sphere = N.central_sphere ∧
            N.IsSeparating := by
  obtain ⟨epsilon₀, hpos, hsmall, htransport⟩ :=
    exists_connected_center_compact_transport.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro F T epsilon E hepos he horn N hN hcenter
  have hhalf : epsilon < 1 / 2 := (he.trans hsmall).trans_lt (by norm_num)
  obtain ⟨N₀, hN₀⟩ := horn.boundary_neck
  let P := spatialNeck N₀ hhalf
  have hp : P.center ∈ horn.carrier :=
    horn_boundary_sphere_subset_carrier horn (hN₀ ▸ P.center_on_central_sphere)
  have hcover : ∀ x ∈ horn.carrier,
      ∃ Q : EpsilonNeck (E.extended.metric T), Q.epsilon = epsilon ∧ Q.center = x := by
    intro x hx
    obtain ⟨Q, hQ⟩ := horn.every_point_neck x hx
    exact ⟨spatialNeck Q hhalf, rfl, hQ⟩
  obtain ⟨e, K, hK, hfix, hsphere⟩ := htransport hepos he horn.carrier
    (horn_isPreconnected_carrier horn) hcover P N rfl hN hp hcenter
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
      (horn_boundary_neck_isSeparating horn N₀ hhalf hN₀)
  refine ⟨e, K, hK, hfix, ?_, hsep⟩
  change e '' N₀.central_sphere = N.central_sphere at hsphere
  rwa [hN₀] at hsphere

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}



noncomputable def horn_neckOnlyCover (horn : StrongHorn E epsilon)
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
    horn_isPreconnected_carrier horn⟩
  necks := {N | N.epsilon = epsilon ∧ N.center ∈ horn.carrier}
  pointwise_center_cover := by
    intro x hx
    obtain ⟨N, hN⟩ := horn.every_point_neck x hx
    let hhalf : epsilon < 1 / 2 :=
      (hsmall.trans A.epsilon₀_le_one_two_hundred).trans_lt (by norm_num)
    refine ⟨spatialNeck N hhalf, ⟨rfl, ?_⟩, hN⟩
    change N.center ∈ horn.carrier
    rw [hN]
    exact hx
  neck_epsilon := fun _ hN => hN.1



theorem exists_horn_neckCap_tube_threshold :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
        (E : GeneralizedFlowExtension F T),
        ∀ (A : RepairedNeckCapTopologyTheory.{u}) (hepos : 0 < epsilon)
          (_he : epsilon ≤ epsilon₀) (hA : epsilon ≤ A.epsilon₀)
          (horn : StrongHorn E epsilon),
        Nonempty (CorrectedA19Conclusion (E.extended.metric T)
          (horn_neckOnlyCover horn A hepos hA)) := by
  obtain ⟨epsilon₀, hpos, hsmall, htransport⟩ := exists_horn_boundary_sphere_transport.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro F T epsilon E A hepos he hA horn
  apply A.a19 (E.extended.metric T) (horn_neckOnlyCover horn A hepos hA) hA
  intro N hN
  obtain ⟨_, _, _, _, _, hsep⟩ := htransport E hepos he horn N hN.1 hN.2
  exact hsep

end PoincareConjecture.M32
