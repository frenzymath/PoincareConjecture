import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.CapConfinement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.TubeCapExclusion.Noncontainment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.TubeRegion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalEnd

theorem exists_strong_neck_tail_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (E : GeneralizedFlowExtension F T) (K : TerminalComponentPath E)
        (e : TerminalEnd K) (A : RepairedNeckCapTopologyTheory.{u})
        {epsilon C B : ℝ},
        0 < epsilon → 0 < C → epsilon ≤ ε₀ → epsilon ≤ A.epsilon₀ →
        (∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x) →
        (∀ D : Set ℝ, IsCompact D →
          IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D)) →
        (∀ x : (E.extended.slice T).carrier,
          B < (E.extended.connection T).scalarCurvature x →
            GeneralizedCanonicalControl (F := E.extended) T x epsilon C) →
        ∃ n : ℕ, ∀ m : ℕ, n ≤ m → ∀ x ∈ e.tail m,
          ∃ N : TerminalStrongNeck E epsilon, N.center = x.val := by
  obtain ⟨ε₀, hε₀, hsmall, hno⟩ := CapCertificate.exists_tube_noncontainment_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro F T E K e A epsilon C B hepsilon hC hε hA hlower hproper hcanonical
  obtain ⟨k, tube, htube⟩ := e.exists_tube_of_canonical_control A
    hepsilon hC hA hlower hproper hcanonical
  obtain ⟨n, _, hn⟩ := e.exists_tail_caps_subset_of_contains_tail
    hlower hproper hC tube.contains_X
  obtain ⟨p, hp⟩ := e.exists_tail_scalar_gt hlower hproper B
  refine ⟨max n p, fun m hnm x hx => ?_⟩
  cases hcanonical x (hp m ((le_max_right _ _).trans hnm) x hx) with
  | neck N hcenter => exact ⟨N, hcenter⟩
  | cap N he hconstant hconnection hxN =>
      exact (hno N tube (he.trans_le hε) (htube.trans_le hε)
        (hn m ((le_max_left _ _).trans hnm) x hx N hconstant
          (N.core_subset_carrier hxN))).elim
  | component N hxN => exact (e.not_mem_cComponent N x.property hxN).elim
  | round N hxN => exact (e.not_mem_roundComponent N x.property hxN).elim

end PoincareConjecture.TerminalEnd
