import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.TubeNonFilling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.HornTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CutGeometry.Conversion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T} (horn : StrongHorn E epsilon)

theorem no_compact_filling_of_contained_neck
    (A : RepairedNeckCapTopologyTheory.{u}) (hεpos : 0 < epsilon)
    (hA : epsilon ≤ A.epsilon₀)
    (N : EpsilonNeck (E.extended.metric T)) (hN : N.epsilon ≤ 1 / 200)
    (hsub : N.carrier ⊆ horn.carrier)
    (K : Set (E.extended.slice T).carrier) (hKsub : K ⊆ horn.carrier)
    (hfront : frontier K = N.central_sphere) (hint : (interior K).Nonempty) :
    ¬ IsCompact K := by
  obtain ⟨Q⟩ := horn.nonempty_neckCap_tube_of_epsilon_le A hεpos hA
  have hε := hA.trans A.epsilon₀_le_one_two_hundred
  obtain ⟨_, _, _, _, _, hsep⟩ := horn.boundary_sphere_smooth_transport_of_epsilon_le hε N hN
    (hsub (N.central_sphere_subset N.center_on_central_sphere))
  exact Q.tube.no_compact_filling_of_contained_neck
    (Q.epsilon_eq.trans_le hε) N hN (hsub.trans Q.contains_X) hsep K
    (hKsub.trans Q.contains_X) hfront hint

end PoincareConjecture.StrongHorn

namespace PoincareConjecture.HornEndCut

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon delta rho : ℝ}
  {E : GeneralizedFlowExtension F T} {horn : StrongHorn E epsilon}
  {N : TerminalStrongNeck E delta}

theorem exists_oriented_surgeryEndCut (cut : HornEndCut horn N rho)
    (A : RepairedNeckCapTopologyTheory.{u}) (hεpos : 0 < epsilon)
    (hA : epsilon ≤ A.epsilon₀) (hdelta : delta ≤ 1 / 200)
    (hN : N.carrier ⊆ horn.carrier) :
    (∃ D : SurgeryEndCut (N.spatialNeck (hdelta.trans_lt (by norm_num))),
      D.tail = cut.carrier) ∨
    (∃ D : SurgeryEndCut (N.reversed.spatialNeck (hdelta.trans_lt (by norm_num))),
      D.tail = cut.carrier) := by
  let hhalf : delta < 1 / 2 := hdelta.trans_lt (by norm_num)
  rcases cut.exists_oriented_surgeryEndCut_or_compact_filling hhalf hN with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨K, hK, hKsub, hfront, hint⟩ := h
    exact False.elim (horn.no_compact_filling_of_contained_neck A hεpos hA
      (N.spatialNeck hhalf) hdelta hN K hKsub hfront hint hK)

end PoincareConjecture.HornEndCut
