import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SmallBallVolume
import PoincareConjecture.Definitions.Ch16.ControlledSurgery

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M47

theorem seed_small_volume_of_larger_cylinder
    {F : SurgeryFlowData.{u}} {T rho r k : ℝ} (hTF : T ∈ F.time_domain)
    (x : (F.slice T).carrier) (hrho : 0 < rho) (hr : 0 < r)
    (hsmall : r ≤ rho) (hk : 0 < k)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-rho ^ 2) 0)
      ((F.metric T).ball x (2 * rho)))
    (hbased : ∀ hs y, y ∈ (F.metric T).ball x (2 * rho) → HEq (e.forward 0 hs y) y)
    (hcurv : ∀ s hs y, y ∈ (F.metric T).ball x (2 * rho) →
      (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤ rho⁻¹ ^ 2)
    (hvolume : ENNReal.ofReal (k * rho ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x rho)) :
    ENNReal.ofReal (Proofs.M46.smallBallLoss * k * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  have hzero : (0 : ℝ) ∈ Icc (-rho ^ 2) 0 := ⟨neg_nonpos.mpr (sq_nonneg rho), le_rfl⟩
  have hterminal (y : (F.slice T).carrier) (hy : y ∈ (F.metric T).ball x (2 * rho)) :
      (F.connection T).curvatureTensorNorm y ≤ rho⁻¹ ^ 2 := by
    have hpoint : (⟨T + 0 / 1, e.forward 0 hzero y⟩ :
        (t : ℝ) × (F.slice t).carrier) = ⟨T, y⟩ :=
      Sigma.ext (by simp) (hbased hzero y hy)
    have hread := congrArg (fun q : (t : ℝ) × (F.slice t).carrier =>
      (F.connection q.1).curvatureTensorNorm q.2) hpoint
    exact hread ▸ hcurv 0 hzero y hy
  exact Proofs.M46.calibrated_small_ball_lower_bound (F.metric T) (F.connection T) x
    hrho hr hsmall hk
    ((F.slices_compact T hTF).of_isClosed_subset isClosed_closure (subset_univ _))
    hterminal hvolume

end PoincareConjecture.M47
