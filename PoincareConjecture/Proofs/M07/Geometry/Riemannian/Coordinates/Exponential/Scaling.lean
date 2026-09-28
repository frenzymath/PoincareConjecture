import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.GeodesicFlow








noncomputable section

namespace PoincareConjecture.CoordinateExponential

open Set Metric
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def velocityScale (c : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E E).prod (c • ContinuousLinearMap.snd ℝ E E)

@[simp] theorem velocityScale_fst (c : ℝ) (z : E × E) :
    (velocityScale c z).1 = z.1 := rfl

@[simp] theorem velocityScale_snd (c : ℝ) (z : E × E) :
    (velocityScale c z).2 = c • z.2 := rfl

theorem coordinateChristoffel_smul_smul
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) (c d : ℝ) :
    coordinateChristoffel B x (c • u) (d • v) =
      (c * d) • coordinateChristoffel B x u v := by
  unfold coordinateChristoffel
  have hK : metricKoszulCovector (fderiv ℝ B x) (c • u) (d • v) =
      (c * d) • metricKoszulCovector (fderiv ℝ B x) u v := by
    ext w
    simp [metricKoszulCovector]
    ring
  rw [hK, map_smul]

theorem coordinateGeodesicField_velocityScale
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (z : E × E) (c : ℝ) :
    coordinateGeodesicField B (velocityScale c z) =
      c • velocityScale c (coordinateGeodesicField B z) := by
  ext <;> simp [coordinateGeodesicField, coordinateChristoffel_smul_smul, smul_smul]



theorem hasDerivAt_velocityScale
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {γ : ℝ → E × E} {c t : ℝ}
    (hγ : HasDerivAt γ (coordinateGeodesicField B (γ (c * t))) (c * t)) :
    HasDerivAt (fun s => velocityScale c (γ (c * s)))
      (coordinateGeodesicField B (velocityScale c (γ (c * t)))) t := by
  have htime := hγ.scomp t ((hasDerivAt_id t).const_mul c)
  have hscale := (velocityScale (E := E) c).hasFDerivAt.comp_hasDerivAt t htime
  simpa only [Function.comp_def, map_smul, mul_one,
    coordinateGeodesicField_velocityScale] using hscale

theorem velocityScale_mem_ball
    {c R : ℝ} (hc : |c| ≤ 1) {x : E} {z : E × E}
    (hz : z ∈ ball (x, 0) R) : velocityScale c z ∈ ball (x, 0) R := by
  rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right] at hz ⊢
  refine ⟨hz.1, ?_⟩
  change ‖c • z.2‖ < R
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_lt (by simpa using hz.2)

end PoincareConjecture.CoordinateExponential
