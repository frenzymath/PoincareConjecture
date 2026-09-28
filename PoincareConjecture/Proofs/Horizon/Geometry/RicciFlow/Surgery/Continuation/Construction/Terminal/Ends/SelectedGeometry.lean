import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.SurgeryInput
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckBoundary








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedContinuationInput

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  {G : GeneralizedRicciFlowData.{u}} {E : GeneralizedFlowExtension G T}
  (N : TerminalStrongNeck E (F.parameters.delta T))
  (hscalar : (E.extended.connection T).scalarCurvature N.center =
    (F.parameters.h T)⁻¹ ^ 2)

include I hscalar in
theorem selected_neck_scale : N.scale = F.parameters.h T := by
  have hh := F.parameters.h_pos T I.terminal_pos.le
  have hn := (N.spatialNeck I.terminal_delta_lt_half).scale_sq_mul_scalar_center_of_connection
    (E.extended.connection T)
  change N.scale ^ 2 * (E.extended.connection T).scalarCurvature N.center = 1 at hn
  rw [hscalar] at hn
  have hcancel : (F.parameters.h T)⁻¹ ^ 2 * (F.parameters.h T) ^ 2 = 1 := by
    field_simp
  have hsq : N.scale ^ 2 = (F.parameters.h T) ^ 2 := by
    calc
      N.scale ^ 2 = N.scale ^ 2 * ((F.parameters.h T)⁻¹ ^ 2 * (F.parameters.h T) ^ 2) := by rw [hcancel, mul_one]
      _ = (F.parameters.h T) ^ 2 := by rw [← mul_assoc, hn, one_mul]
  exact (sq_eq_sq₀ N.scale_pos.le hh.le).mp hsq

include hscalar in
theorem selected_neck_disjoint_low_core :
    Disjoint N.carrier {x | (E.extended.connection T).scalarCurvature x ≤ I.rho⁻¹ ^ 2} := by
  have hh := F.parameters.h_pos T I.terminal_pos.le
  have hδ : F.parameters.delta T < 1 / 200 :=
    I.terminal_delta_bound.trans_lt F.local_constants.delta₀_lt
  have hhρ : F.parameters.h T < I.rho / 2 := by
    have h := mul_lt_mul_of_pos_left hδ I.rho_pos
    linarith [I.terminal_height_rho_delta, I.rho_pos]
  have hinv : 2 * I.rho⁻¹ < (F.parameters.h T)⁻¹ := by
    calc
      2 * I.rho⁻¹ = (I.rho / 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ < (F.parameters.h T)⁻¹ :=
        (inv_lt_inv₀ (div_pos I.rho_pos (by norm_num)) hh).mpr hhρ
  have hlevel : I.rho⁻¹ ^ 2 < (F.parameters.h T)⁻¹ ^ 2 / 2 := by
    have hρinv := inv_pos.mpr I.rho_pos
    have hhinv := inv_pos.mpr hh
    nlinarith [sq_pos_of_pos hρinv]
  apply disjoint_left.mpr
  intro x hx hlow
  have h := (N.scalar_strictly_within_factor_two_on_carrier hδ.le hx).1
  rw [hscalar] at h
  exact (not_lt_of_ge hlow) (hlevel.trans h)

end PoincareConjecture.RepairedContinuationInput
