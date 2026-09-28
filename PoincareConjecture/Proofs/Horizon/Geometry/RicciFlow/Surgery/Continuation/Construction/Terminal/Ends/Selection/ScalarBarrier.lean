import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.Ambient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CutGeometry.Sides

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal

theorem linear_boundary_lt_half_height_scalar {rho delta C h : ℝ}
    (hrho : 0 < rho) (hC : 0 < C) (hh : 0 < h)
    (hdelta : delta ≤ 1 / 200)
    (hhd : h ≤ rho * delta) (hhC : h ≤ rho / (2 * C)) :
    32 * C * rho⁻¹ ^ 2 < h⁻¹ ^ 2 / 2 := by
  have ha : h ≤ rho / 200 := by
    calc
      h ≤ rho * delta := hhd
      _ ≤ rho * (1 / 200) := mul_le_mul_of_nonneg_left hdelta hrho.le
      _ = rho / 200 := by ring
  have hb : 2 * C * h ≤ rho := by
    nlinarith [(le_div_iff₀ (by positivity : 0 < 2 * C)).mp hhC]
  have hprod := mul_le_mul ha hb (by positivity : 0 ≤ 2 * C * h)
    (by positivity : 0 ≤ rho / 200)
  have hsmall : 64 * C * h ^ 2 < rho ^ 2 := by
    nlinarith [mul_pos hC (sq_pos_of_pos hh)]
  apply (mul_lt_mul_iff_left₀ (mul_pos (sq_pos_of_pos hrho) (sq_pos_of_pos hh))).mp
  have hleft : 32 * C * rho⁻¹ ^ 2 * (rho ^ 2 * h ^ 2) = 32 * C * h ^ 2 := by
    field_simp
  have hright : h⁻¹ ^ 2 / 2 * (rho ^ 2 * h ^ 2) = rho ^ 2 / 2 := by
    field_simp
  rw [hleft, hright]
  linarith

end PoincareConjecture.Surgery.Terminal

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T} (horn : StrongHorn E epsilon)

theorem neck_carrier_subset_of_overlap_of_linear_boundary
    {delta rho C h : ℝ} (N : TerminalStrongNeck E delta)
    (hdelta : delta ≤ 1 / 200) (hrho : 0 < rho) (hC : 0 < C) (hh : 0 < h)
    (hhd : h ≤ rho * delta) (hhC : h ≤ rho / (2 * C))
    (hlevel : (E.extended.connection T).scalarCurvature N.center = h⁻¹ ^ 2)
    (hboundary : ∀ x ∈ horn.boundary_sphere,
      (E.extended.connection T).scalarCurvature x < 32 * C * rho⁻¹ ^ 2)
    (hmeet : (N.carrier ∩ horn.carrier).Nonempty) : N.carrier ⊆ horn.carrier := by
  have hhalf : delta < 1 / 2 := by linarith
  apply horn.subset_carrier_of_isPreconnected (N.spatialNeck hhalf).isConnected_carrier.isPreconnected
    hmeet
  apply disjoint_left.mpr
  intro x hx hb
  have hlower := ((N.spatialNeck hhalf).scalar_within_factor_two_on_carrier
    (E.extended.connection T) hdelta hx).1
  change (E.extended.connection T).scalarCurvature N.center / 2 ≤
    (E.extended.connection T).scalarCurvature x at hlower
  rw [hlevel] at hlower
  exact (not_lt_of_ge ((Surgery.Terminal.linear_boundary_lt_half_height_scalar
    hrho hC hh hdelta hhd hhC).le.trans hlower)) (hboundary x hb)

end PoincareConjecture.StrongHorn
