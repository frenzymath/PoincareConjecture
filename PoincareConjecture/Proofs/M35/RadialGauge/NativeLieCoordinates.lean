import PoincareConjecture.Proofs.M35.Uniqueness.VectorHeatEnergy
import PoincareConjecture.Proofs.M03.Existence.IntrinsicLieMetricNative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.RadialGauge

open Uniqueness DeTurckNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)


theorem metricLieDerivative_euclidean_pair {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {W : V → V} (hW : ContDiff ℝ ∞ W) (x u v : V) :
    metricLieDerivative D W x u v =
      fderiv ℝ (fun y => g.inner y u v) x (W x) +
        g.inner x (fderiv ℝ W x u) v + g.inner x u (fderiv ℝ W x v) := by
  have h := metricLieDerivative_on_fields D W (fun _ => u) (fun _ => v)
    ((euclidean_field_contMDiff hW).mdifferentiable (by simp) x)
    ((euclidean_field_contMDiff (contDiff_const (c := u))).mdifferentiable (by simp) x)
    ((euclidean_field_contMDiff (contDiff_const (c := v))).mdifferentiable (by simp) x)
  have hb (z : V) : VectorField.mlieBracket (𝓡 n) W (fun _ => z) x =
      -fderiv ℝ W x z := by
    simp only [VectorField.mlieBracket,
      VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin, fderivWithin_univ, fderiv_const_apply,
      zero_apply, zero_sub]
  rw [hb, hb] at h
  have hm : mvfderiv (𝓡 n) (fun y => g.inner y u v) x (W x) =
      fderiv ℝ (fun y => g.inner y u v) x (W x) := by
    rw [mvfderiv, mfderiv_eq_fderiv]
    rfl
  rw [hm] at h
  simpa only [map_neg, neg_apply, sub_neg_eq_add] using h

end PoincareConjecture.M35.RadialGauge
