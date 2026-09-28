import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicWarping
import PoincareConjecture.Proofs.M35.Mathlib.SmoothEvenRadial









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial

private noncomputable def profileMap (f : ℝ → ℝ) (x : StandardCapSpace) :
    StandardCapSpace := axisDivision f ‖x‖ • x

private theorem profileMap_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (ho : Function.Odd f) : ContDiff ℝ ∞ (profileMap f) :=
  (contDiff_even_norm (axisDivision_contDiff hf)
    (axisDivision_even_of_odd hf ho)).smul contDiff_id

private theorem profileMap_norm {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hz : f 0 = 0) (hp : ∀ r : ℝ, 0 < r → 0 < f r) (x : StandardCapSpace) :
    ‖profileMap f x‖ = f ‖x‖ := by
  by_cases hx : x = 0
  · simp only [hx, profileMap, norm_zero, smul_zero, hz]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hmul : ‖x‖ * axisDivision f ‖x‖ = f ‖x‖ := by
    simpa only [hz, sub_zero] using mul_axisDivision hf ‖x‖
  have hd : 0 < axisDivision f ‖x‖ :=
    (mul_pos_iff_of_pos_left hr).mp (hmul.symm ▸ hp ‖x‖ hr)
  rw [profileMap, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos hd, mul_comm]
  exact hmul

private theorem profileMap_inverse {f q : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hq : ContDiff ℝ ∞ q) (hf0 : f 0 = 0) (hq0 : q 0 = 0)
    (hp : ∀ r : ℝ, 0 < r → 0 < f r) (hinv : ∀ r : ℝ, q (f r) = r)
    (x : StandardCapSpace) : profileMap q (profileMap f x) = x := by
  by_cases hx : x = 0
  · simp only [hx, profileMap, norm_zero, smul_zero]
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hfprod : ‖x‖ * axisDivision f ‖x‖ = f ‖x‖ := by
    simpa only [hf0, sub_zero] using mul_axisDivision hf ‖x‖
  have hqprod : f ‖x‖ * axisDivision q (f ‖x‖) = ‖x‖ := by
    simpa only [hq0, sub_zero, hinv] using mul_axisDivision hq (f ‖x‖)
  have hcoeff : axisDivision q (f ‖x‖) * axisDivision f ‖x‖ = 1 := by
    apply mul_left_cancel₀ hr
    calc
      ‖x‖ * (axisDivision q (f ‖x‖) * axisDivision f ‖x‖) =
          (‖x‖ * axisDivision f ‖x‖) * axisDivision q (f ‖x‖) := by ring
      _ = ‖x‖ * 1 := by rw [hfprod, hqprod, mul_one]
  change axisDivision q ‖profileMap f x‖ • (axisDivision f ‖x‖ • x) = x
  rw [profileMap_norm hf hf0 hp, smul_smul, hcoeff, one_smul]

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)


noncomputable def intrinsicSpatialCoordinate (x : StandardCapSpace) : StandardCapSpace :=
  profileMap (radialArclength g) x


noncomputable def intrinsicSpatialInverse (x : StandardCapSpace) : StandardCapSpace :=
  profileMap (radialArclengthOrderIso g hrotation hcomplete).symm x

include hrotation in
theorem intrinsicSpatialCoordinate_contDiff :
    ContDiff ℝ ∞ (intrinsicSpatialCoordinate g) :=
  profileMap_contDiff (radialArclength_contDiff g) (radialArclength_odd g hrotation)

theorem intrinsicSpatialInverse_contDiff :
    ContDiff ℝ ∞ (intrinsicSpatialInverse g hrotation hcomplete) :=
  profileMap_contDiff (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete)
    (radialArclengthOrderIso_symm_odd g hrotation hcomplete)

theorem intrinsicSpatialCoordinate_norm (x : StandardCapSpace) :
    ‖intrinsicSpatialCoordinate g x‖ = radialArclength g ‖x‖ := by
  apply profileMap_norm (radialArclength_contDiff g) (radialArclength_zero g)
  intro r hr
  simpa only [radialArclength_zero] using radialArclength_strictMono g hr

theorem intrinsicSpatialInverse_norm (x : StandardCapSpace) :
    ‖intrinsicSpatialInverse g hrotation hcomplete x‖ =
      (radialArclengthOrderIso g hrotation hcomplete).symm ‖x‖ :=
  profileMap_norm (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete)
    (radialArclengthOrderIso_symm_zero g hrotation hcomplete)
    (fun _ hr => radialArclengthOrderIso_symm_pos g hrotation hcomplete hr) x

theorem intrinsicSpatialInverse_coordinate (x : StandardCapSpace) :
    intrinsicSpatialInverse g hrotation hcomplete (intrinsicSpatialCoordinate g x) = x := by
  apply profileMap_inverse (radialArclength_contDiff g)
    (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete)
    (radialArclength_zero g) (radialArclengthOrderIso_symm_zero g hrotation hcomplete)
  · intro r hr
    simpa only [radialArclength_zero] using radialArclength_strictMono g hr
  · exact (radialArclengthOrderIso g hrotation hcomplete).symm_apply_apply

theorem intrinsicSpatialCoordinate_inverse (x : StandardCapSpace) :
    intrinsicSpatialCoordinate g (intrinsicSpatialInverse g hrotation hcomplete x) = x := by
  apply profileMap_inverse (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete)
    (radialArclength_contDiff g) (radialArclengthOrderIso_symm_zero g hrotation hcomplete)
    (radialArclength_zero g)
  · exact fun _ hr => radialArclengthOrderIso_symm_pos g hrotation hcomplete hr
  · exact (radialArclengthOrderIso g hrotation hcomplete).apply_symm_apply


noncomputable def intrinsicSpatialDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ where
  toEquiv :=
    { toFun := intrinsicSpatialCoordinate g
      invFun := intrinsicSpatialInverse g hrotation hcomplete
      left_inv := intrinsicSpatialInverse_coordinate g hrotation hcomplete
      right_inv := intrinsicSpatialCoordinate_inverse g hrotation hcomplete }
  contMDiff_toFun := (intrinsicSpatialCoordinate_contDiff g hrotation).contMDiff
  contMDiff_invFun := (intrinsicSpatialInverse_contDiff g hrotation hcomplete).contMDiff

theorem intrinsicSpatialCoordinate_zero : intrinsicSpatialCoordinate g 0 = 0 := by
  simp only [intrinsicSpatialCoordinate, profileMap, smul_zero]

theorem intrinsicSpatialInverse_zero : intrinsicSpatialInverse g hrotation hcomplete 0 = 0 := by
  simp only [intrinsicSpatialInverse, profileMap, smul_zero]

end PoincareConjecture.M35.Uniqueness
