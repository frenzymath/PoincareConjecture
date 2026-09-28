import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Calibration
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem cap_disjoint_low_core_of_high_point (Q : SingularLimitConclusion H)
    (cap : CapCertificate (Q.extension.extended.metric T))
    (rho : ℝ) (hconstant : 1 ≤ H.constant) (hcap : cap.cap_constant ≤ 2 * H.constant)
    (hhigh : ∃ x ∈ cap.carrier, 2 * H.constant ^ 2 * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x) :
    Disjoint cap.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} := by
  obtain ⟨x, hx, hxhigh⟩ := hhigh
  have heq (z) : cap.connection.scalarCurvature z = Q.terminal_scalar z := by
    rw [Q.terminal_scalar_eq]
    exact cap.connection.scalarCurvature_eq _ z
  refine disjoint_left.mpr fun y hy hylow => ?_
  have hratio := cap.scalar_lt_constant_mul hy hx
  rw [heq x, heq y] at hratio
  have hpos : 0 < Q.terminal_scalar y := by
    rw [← heq y]
    exact cap.scalar_pos y hy
  have hupper := (mul_le_mul_of_nonneg_right hcap hpos.le).trans
    (mul_le_mul_of_nonneg_left hylow (by positivity : 0 ≤ 2 * H.constant))
  have hC : H.constant ≤ H.constant ^ 2 := by
    nlinarith [sq_nonneg (H.constant - 1)]
  have hlevel : 2 * H.constant * rho⁻¹ ^ 2 ≤ 2 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by norm_num))
      (sq_nonneg _)
  exact (not_lt_of_ge (hlevel.trans hxhigh)) (hratio.trans_le hupper)

theorem endRegionCover_cap_disjoint_low_core (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u})
    (haccuracy : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier) (hX : IsConnected X)
    (hcomponent : X ⊆ K.component)
    (hscalar : ∀ x ∈ X, H.r₀⁻¹ ^ 2 < Q.terminal_scalar x)
    (rho : ℝ) (hconstant : 1 ≤ H.constant)
    (hlower : ∀ x ∈ X, 2 * H.constant ^ 2 * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x)
    (cap : CapCertificate (Q.extension.extended.metric T))
    (hcap : cap ∈ (Q.endRegionCover A haccuracy K e X hX hcomponent hscalar).caps) :
    Disjoint cap.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} := by
  obtain ⟨hepsilon, hbound, hconnection, x, hxcore, hxX⟩ := hcap
  exact Q.cap_disjoint_low_core_of_high_point cap rho hconstant hbound
    ⟨x, cap.core_subset_carrier hxcore, hlower x hxX⟩

end PoincareConjecture.SingularLimitConclusion
