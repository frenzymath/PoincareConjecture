import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicWarping
import PoincareConjecture.Proofs.M35.RawFlow.ScalarFloor
import PoincareConjecture.Proofs.M35.RawFlow.SectionalPreservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

theorem raw_intrinsic_warping_controls
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Ico 0 G.lifetime)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
            (G.flow.metric t).inner x u v) :
    let f := intrinsicWarpingRadius (G.flow.metric t) hrotation (G.complete P ht)
    ∀ s > 0, 0 < f s ∧ f s ^ 2 ≤ 2 * H.scalar_constant ∧
      0 ≤ deriv f s ∧ deriv f s ≤ 1 ∧ deriv (deriv f) s ≤ 0 ∧ s * deriv f s ≤ f s := by
  intro f s hs
  let g := G.flow.metric t
  let r := (radialArclengthOrderIso g hrotation (G.complete P ht)).symm s
  have hr : 0 < r := radialArclengthOrderIso_symm_pos g hrotation (G.complete P ht) hs
  have hsec := raw_nonnegative_sectional P G ht
  have hfirst : deriv f s = axisWarpingSlope g r :=
    (intrinsicWarpingRadius_hasDerivAt g hrotation (G.complete P ht) hs).deriv
  have hsecond : deriv (deriv f) s = axisWarpingSecond g r :=
    (intrinsicWarpingRadius_deriv_hasDerivAt g hrotation (G.complete P ht) hs).deriv
  have hrad : axisWarpingRadius g r ^ 2 ≤ 2 * H.scalar_constant := by
    have hh := axisWarpingRadius_sq_le_of_exterior_scalar_floor (G.flow.connection t)
      hrotation (G.complete P ht) hsec (inv_pos.mpr H.scalar_constant_pos)
      (K := ∅) isCompact_empty (fun x _ => raw_scalar_floor P H G ht x) hr
    simpa only [div_inv_eq_mul] using hh
  refine ⟨intrinsicWarpingRadius_pos g hrotation (G.complete P ht) hs, hrad, ?_, ?_, ?_, ?_⟩
  · rw [hfirst]
    exact axisWarpingSlope_nonneg (G.flow.connection t) hrotation hsec (G.complete P ht) hr
  · rw [hfirst]
    exact axisWarpingSlope_le_one (G.flow.connection t) hrotation hsec hr
  · rw [hsecond]
    exact axisWarpingSecond_nonpos (G.flow.connection t) hrotation hsec hr
  · have hh := axisWarpingSlope_mul_arclength_le (G.flow.connection t) hrotation hsec hr
    have heq : radialArclength g r = s :=
      (radialArclengthOrderIso g hrotation (G.complete P ht)).apply_symm_apply s
    rw [heq, mul_comm, ← hfirst] at hh
    exact hh

end PoincareConjecture.M35.Uniqueness
