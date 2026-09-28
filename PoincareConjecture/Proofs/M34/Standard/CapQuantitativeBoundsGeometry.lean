import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameterRecut
import PoincareConjecture.Proofs.M34.Standard.LocalCalibratedImageVolume
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)



theorem intrinsicDiameter_lt_of_normalized_base
    {C : ℝ} (hC : N.cap_constant ≤ C)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1) :
    intrinsicDiameter g N.carrier < ENNReal.ofReal C := by
  have hs := (N.scalarSup_bounds_of_normalized_base ho hnormal hC).1
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hs (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  refine N.intrinsic_diameter_bound.trans_le (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ N.cap_constant * 1 := mul_le_mul_of_nonneg_left hp N.cap_constant_pos.le
    _ ≤ C := by simpa only [mul_one] using hC



theorem volume_lt_of_normalized_base
    {C : ℝ} (hC : N.cap_constant ≤ C)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1) :
    calibratedMetricVolume g N.carrier < ENNReal.ofReal C := by
  have hs := (N.scalarSup_bounds_of_normalized_base ho hnormal hC).1
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hs (by norm_num : (-3 / 2 : ℝ) ≤ 0)
  refine N.volume_bound.trans_le ?_
  calc
    _ ≤ ENNReal.ofReal N.cap_constant * ENNReal.ofReal 1 :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal hp) _
    _ ≤ ENNReal.ofReal C := by simpa using ENNReal.ofReal_le_ofReal hC



theorem image_recut_intrinsicDiameter_lt
    {C : ℝ} (hC : N.cap_constant ≤ C)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    (h : RiemannianMetric 3 X) (f : M → X) {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f (N.recutCarrier b))
    (hbound : ∀ x ∈ N.recutCarrier b, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ 2 * g.tangentNorm x v) :
    intrinsicDiameter h (f '' N.recutCarrier b) < ENNReal.ofReal (4 * C) := by
  have hmap := g.intrinsicDiameter_image_le_mul_of_isOpen h f
    (N.recutCarrier_isOpen hb hb') hf (by norm_num : (0 : ℝ) < 2) hbound
  have hrecut := N.recutCarrier_intrinsicDiameter_le_two hb hb'
  have hdiam := N.intrinsicDiameter_lt_of_normalized_base hC ho hnormal
  calc
    _ ≤ ENNReal.ofReal 2 * intrinsicDiameter g (N.recutCarrier b) := hmap
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal 2 * intrinsicDiameter g N.carrier) :=
      mul_le_mul_right hrecut _
    _ = 4 * intrinsicDiameter g N.carrier := by norm_num; ring
    _ < 4 * ENNReal.ofReal C :=
      (ENNReal.mul_right_strictMono (by norm_num) (by norm_num)) hdiam
    _ = ENNReal.ofReal (4 * C) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num




theorem image_recut_volume_lt
    [MeasurableSpace X] [BorelSpace X] [T3Space X] [SecondCountableTopology M]
    {C : ℝ} (hC : N.cap_constant ≤ C)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    (h : RiemannianMetric 3 X) (e : OpenPartialHomeomorph M X) {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹)
    (hsource : N.recutCarrier b ⊆ e.source)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source)
    (hbound : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤ 2 * g.tangentNorm x v) :
    calibratedMetricVolume h (e '' N.recutCarrier b) < ENNReal.ofReal (8 * C) := by
  have hmap := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le
    g h e hf (by norm_num : (0 : ℝ) < 2) hbound
    (N.recutCarrier_isOpen hb hb').measurableSet hsource
  have hsub := (calibratedMetricVolume g).mono (N.recutCarrier_subset_carrier b)
  have hvolume := N.volume_lt_of_normalized_base hC ho hnormal
  calc
    _ ≤ ENNReal.ofReal 2 ^ 3 * calibratedMetricVolume g (N.recutCarrier b) := hmap
    _ ≤ ENNReal.ofReal 2 ^ 3 * calibratedMetricVolume g N.carrier :=
      mul_le_mul_right hsub _
    _ = 8 * calibratedMetricVolume g N.carrier := by norm_num
    _ < 8 * ENNReal.ofReal C :=
      (ENNReal.mul_right_strictMono (by norm_num) (by norm_num)) hvolume
    _ = ENNReal.ofReal (8 * C) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

end PoincareConjecture.CapCertificate
