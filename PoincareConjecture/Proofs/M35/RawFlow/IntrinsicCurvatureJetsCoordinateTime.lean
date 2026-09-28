import PoincareConjecture.Proofs.M35.RawFlow.ArclengthTimeDerivative
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialCoordinate

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial

theorem intrinsicSpatialCoordinate_eq_quotient
    (g : RiemannianMetric 3 StandardCapSpace) {x : StandardCapSpace} (hx : x ≠ 0) :
    intrinsicSpatialCoordinate g x = (radialArclength g ‖x‖ / ‖x‖) • x := by
  change axisDivision (radialArclength g) ‖x‖ • x = _
  congr 1
  apply (eq_div_iff (norm_ne_zero_iff.mpr hx)).mpr
  rw [mul_comm, mul_axisDivision (radialArclength_contDiff g),
    radialArclength_zero, sub_zero]

theorem intrinsicSpatialVelocity_contDiff
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hcomplete : MetricComplete g) :
    ContDiff ℝ ∞ (fun x : StandardCapSpace =>
      axisDivision (intrinsicRadialVelocity g hrotation hcomplete)
        ‖intrinsicSpatialCoordinate g x‖ • intrinsicSpatialCoordinate g x) :=
  ((intrinsicRadialVelocity_quotient_contDiff_norm g hrotation hcomplete).comp
    (intrinsicSpatialCoordinate_contDiff g hrotation)).smul
      (intrinsicSpatialCoordinate_contDiff g hrotation)

theorem raw_intrinsicSpatialCoordinate_hasDerivAt
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀) {t : ℝ}
    (ht : t ∈ Ioo 0 G.lifetime)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    (hcomplete : MetricComplete (G.flow.metric t)) (x : StandardCapSpace) :
    HasDerivAt (fun s => intrinsicSpatialCoordinate (G.flow.metric s) x)
      (axisDivision (intrinsicRadialVelocity (G.flow.metric t) hrotation hcomplete)
        ‖intrinsicSpatialCoordinate (G.flow.metric t) x‖ •
          intrinsicSpatialCoordinate (G.flow.metric t) x) t := by
  by_cases hx : x = 0
  · simpa only [hx, intrinsicSpatialCoordinate_zero, smul_zero] using
      hasDerivAt_const t (0 : StandardCapSpace)
  have heq : (fun s => intrinsicSpatialCoordinate (G.flow.metric s) x) =
      fun s => (radialArclength (G.flow.metric s) ‖x‖ / ‖x‖) • x :=
    funext (fun s => intrinsicSpatialCoordinate_eq_quotient (G.flow.metric s) hx)
  have hv : HasDerivAt
      (fun s => (radialArclength (G.flow.metric s) ‖x‖ / ‖x‖) • x)
      ((intrinsicRadialVelocity (G.flow.metric t) hrotation hcomplete
        (radialArclength (G.flow.metric t) ‖x‖) / ‖x‖) • x) t :=
    ((raw_radialArclength_hasDerivAt_velocity G ht hrotation hcomplete
      (norm_nonneg x)).div_const ‖x‖).smul_const x
  rw [heq]
  have heqv : axisDivision (intrinsicRadialVelocity (G.flow.metric t) hrotation hcomplete)
        ‖intrinsicSpatialCoordinate (G.flow.metric t) x‖ •
          intrinsicSpatialCoordinate (G.flow.metric t) x =
      (intrinsicRadialVelocity (G.flow.metric t) hrotation hcomplete
        (radialArclength (G.flow.metric t) ‖x‖) / ‖x‖) • x := by
    rw [intrinsicSpatialCoordinate_norm,
      intrinsicSpatialCoordinate_eq_quotient (G.flow.metric t) hx, smul_smul]
    congr 1
    rw [← mul_div_assoc, mul_comm _ (radialArclength (G.flow.metric t) ‖x‖),
      mul_axisDivision (intrinsicRadialVelocity_contDiff (G.flow.metric t) hrotation hcomplete),
      intrinsicRadialVelocity_zero, sub_zero]
  rw [heqv]
  exact hv

end PoincareConjecture.M35.Uniqueness
