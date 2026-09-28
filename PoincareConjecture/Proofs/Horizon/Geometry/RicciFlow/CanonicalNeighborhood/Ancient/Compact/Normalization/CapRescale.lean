import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.CapScaling
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

private theorem cap_inverse_half_power {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    (c⁻¹ * R) ^ (-1 / 2 : ℝ) = Real.sqrt c * R ^ (-1 / 2 : ℝ) := by
  rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hR.le, Real.inv_rpow hc.le,
    neg_div, Real.rpow_neg hc.le, inv_inv, Real.sqrt_eq_rpow]

private theorem cap_inverse_three_halves_power {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    (c⁻¹ * R) ^ (-3 / 2 : ℝ) = Real.sqrt c ^ 3 * R ^ (-3 / 2 : ℝ) := by
  rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hR.le, Real.inv_rpow hc.le,
    neg_div, Real.rpow_neg hc.le, inv_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  norm_num

private theorem cap_three_halves_power {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    (c⁻¹ * R) ^ (3 / 2 : ℝ) =
      (c⁻¹ * (Real.sqrt c)⁻¹) * R ^ (3 / 2 : ℝ) := by
  rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hR.le, Real.inv_rpow hc.le,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hc, Real.rpow_one, mul_inv,
    Real.sqrt_eq_rpow]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

def CapCertificate.rescale (A : CapCertificate g) (c : ℝ) (hc : 0 < c) :
    CapCertificate (rescaledMetric g c hc) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hne : ENNReal.ofReal (Real.sqrt c) ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hball (y : M) :
      (rescaledMetric g c hc).ball y (Real.sqrt c * A.core_radius y) =
        g.ball y (A.core_radius y) := by
    rw [rescaledMetric_ball, mul_div_cancel_left₀ _ hs.ne']
  refine { A with
    connection := rescaledMetric_connection g A.connection c hc
    end_neck := A.end_neck.rescale c hc
    end_neck_connection := by
      change rescaledMetric_connection g A.end_neck.connection c hc = _
      rw [A.end_neck_connection]
    boundary_neck := A.boundary_neck.rescale c hc
    boundary_neck_connection := by
      change rescaledMetric_connection g A.boundary_neck.connection c hc = _
      rw [A.boundary_neck_connection]
    scalar_pos := ?_
    intrinsic_diameter_bound := ?_
    scalar_ratio := ?_
    volume_bound := ?_
    core_radius := fun y => Real.sqrt c * A.core_radius y
    core_radius_pos := fun y hy => mul_pos hs (A.core_radius_pos y hy)
    core_radius_eq := ?_
    core_ball_subset := by simpa only [hball] using A.core_ball_subset
    core_ball_compact := by simpa only [hball] using A.core_ball_compact
    core_ball_volume_lower := ?_
    gradient_bound := ?_
    laplacian_bound := ?_
  }
  · intro x hx
    rw [rescaledMetric_scalarCurvature]
    exact mul_pos (inv_pos.mpr hc) (A.scalar_pos x hx)
  · rw [rescaledMetric_intrinsicDiameter, rescaledMetric_scalarCurvatureSupOn,
      cap_inverse_half_power hc A.scalar_sup_pos,
      show A.cap_constant * (Real.sqrt c * scalarCurvatureSupOn g A.connection A.carrier ^
        (-1 / 2 : ℝ)) = Real.sqrt c * (A.cap_constant *
          scalarCurvatureSupOn g A.connection A.carrier ^ (-1 / 2 : ℝ)) by ring,
      ENNReal.ofReal_mul hs.le]
    simpa only [mul_comm] using
      ENNReal.mul_lt_mul_left hne ENNReal.ofReal_ne_top A.intrinsic_diameter_bound
  · obtain ⟨b, hb, hbound⟩ := A.scalar_ratio
    refine ⟨b, hb, fun x hx y hy => ?_⟩
    simp only [rescaledMetric_scalarCurvature]
    calc
      _ ≤ c⁻¹ * (b * A.connection.scalarCurvature x) :=
        mul_le_mul_of_nonneg_left (hbound x hx y hy) (inv_nonneg.mpr hc.le)
      _ = _ := by ring
  · rw [rescaledMetric_calibratedMetricVolume, rescaledMetric_scalarCurvatureSupOn,
      cap_inverse_three_halves_power hc A.scalar_sup_pos,
      ENNReal.ofReal_mul (pow_nonneg hs.le _), ENNReal.ofReal_pow hs.le]
    have h := ENNReal.mul_lt_mul_left (pow_ne_zero 3 hne)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) A.volume_bound
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  · intro y hy
    rw [hball, rescaledMetric_scalarCurvatureSupOn, A.core_radius_eq y hy, mul_inv, mul_pow]
    simp only [inv_pow, Real.sq_sqrt hc.le]
  · obtain ⟨b, hb, hbound⟩ := A.core_ball_volume_lower
    refine ⟨b, hb, fun y hy => ?_⟩
    rw [hball, rescaledMetric_calibratedMetricVolume,
      mul_pow, show b * (Real.sqrt c ^ 3 * A.core_radius y ^ 3) =
        Real.sqrt c ^ 3 * (b * A.core_radius y ^ 3) by ring,
      ENNReal.ofReal_mul (pow_nonneg hs.le _), ENNReal.ofReal_pow hs.le]
    exact mul_le_mul_right (hbound y hy) _
  · obtain ⟨b, hb, hbound⟩ := A.gradient_bound
    refine ⟨b, hb, fun x hx => ?_⟩
    rw [rescaledMetric_scalarGradientNorm, rescaledMetric_scalarCurvature,
      cap_three_halves_power hc (A.scalar_pos x hx)]
    calc
      _ ≤ (c⁻¹ * (Real.sqrt c)⁻¹) *
          (b * A.connection.scalarCurvature x ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hbound x hx) (by positivity)
      _ = _ := by ring
  · obtain ⟨b, hb, hbound⟩ := A.laplacian_bound
    refine ⟨b, hb, fun x hx => ?_⟩
    rw [rescaledMetric_scalarEvolution, abs_mul, abs_of_nonneg (sq_nonneg _),
      rescaledMetric_scalarCurvature, mul_pow]
    calc
      _ ≤ c⁻¹ ^ 2 * (b * A.connection.scalarCurvature x ^ 2) :=
        mul_le_mul_of_nonneg_left (hbound x hx) (sq_nonneg _)
      _ = _ := by ring

section MetricCast

omit [T2Space M]

def CapCertificate.castMetric {h : RiemannianMetric 3 M} (e : g = h)
    (A : CapCertificate g) : CapCertificate h := e ▸ A

@[simp] theorem CapCertificate.castMetric_epsilon {h : RiemannianMetric 3 M}
    (e : g = h) (A : CapCertificate g) : (A.castMetric e).epsilon = A.epsilon := by
  subst h
  rfl

@[simp] theorem CapCertificate.castMetric_cap_constant {h : RiemannianMetric 3 M}
    (e : g = h) (A : CapCertificate g) : (A.castMetric e).cap_constant = A.cap_constant := by
  subst h
  rfl

@[simp] theorem CapCertificate.castMetric_carrier {h : RiemannianMetric 3 M}
    (e : g = h) (A : CapCertificate g) : (A.castMetric e).carrier = A.carrier := by
  subst h
  rfl

@[simp] theorem CapCertificate.castMetric_core {h : RiemannianMetric 3 M}
    (e : g = h) (A : CapCertificate g) : (A.castMetric e).core = A.core := by
  subst h
  rfl

@[simp] theorem CapCertificate.castMetric_closed_core {h : RiemannianMetric 3 M}
    (e : g = h) (A : CapCertificate g) : (A.castMetric e).closed_core = A.closed_core := by
  subst h
  rfl

@[simp] theorem CapCertificate.castMetric_model_kind {h : RiemannianMetric 3 M}
    (e : g = h) (A : CapCertificate g) : (A.castMetric e).model_kind = A.model_kind := by
  subst h
  rfl

@[simp] theorem CapCertificate.castMetric_puncture {h : RiemannianMetric 3 M}
    (e : g = h) (A : CapCertificate g) : (A.castMetric e).puncture = A.puncture := by
  subst h
  rfl

@[simp] theorem CapCertificate.castMetric_boundary_sphere {h : RiemannianMetric 3 M}
    (e : g = h) (A : CapCertificate g) :
    (A.castMetric e).boundary_sphere = A.boundary_sphere := by
  subst h
  rfl

@[simp] theorem CapCertificate.castMetric_core_radius {h : RiemannianMetric 3 M}
    (e : g = h) (A : CapCertificate g) : (A.castMetric e).core_radius = A.core_radius := by
  subst h
  rfl

end MetricCast

end PoincareConjecture
