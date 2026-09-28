import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.BoundaryClearance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Calibration



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}




theorem exists_eventually_cap_core_uniform_clearance
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t),
          N.epsilon ≤ CapCertificate.coreBallClearanceThreshold.{u} →
          N.cap_constant ≤ H.constant → N.connection = F.connection t →
          H.reference.forward t ht x₀ ∈ N.core →
          ∀ p ∈ N.core, ∀ y ∉ N.carrier,
            ENNReal.ofReal (N.core_radius p + δ) ≤ (F.metric t).edist p y := by
  let B := (H.terminalConnection P04).scalarCurvature x₀ + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let δ := (H.constant * B) ^ (-1 / 2 : ℝ)
  have hδ : 0 < δ := Real.rpow_pos_of_pos (mul_pos H.constant_pos hB) _
  refine ⟨δ, hδ, ?_⟩
  have hlate : ∀ᶠ t in 𝓝[<] T, H.reference.scalar t x₀ < B :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Iio_mem_nhds (lt_add_one _))
  filter_upwards [hlate] with t hlate
  intro ht N hε hconstant hconnection hx₀core p hp y hy
  have hx₀carrier := N.core_subset_carrier hx₀core
  have hpos := N.scalar_pos _ hx₀carrier
  have hscale := (N.neck_scales_lower_of_constant_le hconstant hx₀carrier).2
  rw [hconnection, H.reference.scalar_pullback] at hpos hscale
  have hpow : δ ≤ (H.constant * H.reference.scalar t x₀) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos H.constant_pos hpos)
      (mul_le_mul_of_nonneg_left hlate.le H.constant_pos.le) (by norm_num)
  have hscale' : δ ≤ N.boundary_neck.scale := hpow.trans hscale.le
  have hinv : 200 ≤ N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    linarith [N.epsilon_le_threshold]
  have hbuffer : δ ≤ (0.8 : ℝ) * N.boundary_neck.scale * N.epsilon⁻¹ := by
    have hm := mul_le_mul_of_nonneg_left hinv N.boundary_neck.scale_pos.le
    nlinarith [N.boundary_neck.scale_pos]
  exact (ENNReal.ofReal_le_ofReal (add_le_add (le_refl (N.core_radius p)) hbuffer)).trans
    (N.core_ball_clearance hε hp hy)

end PoincareConjecture.SingularTimeAssumptions
