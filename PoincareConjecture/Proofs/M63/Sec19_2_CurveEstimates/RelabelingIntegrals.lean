import PoincareConjecture.Proofs.M63.Mathlib.PeriodicChangeOfVariables
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SmoothRelabeling
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.RatioRegularity
import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) (d : ℝ → ℝ → M)
  {phi : ℝ → ℝ} {t : ℝ}

theorem integral_density_comp
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ x, 0 < deriv phi x)
    (A : ℝ → ℝ) (hA : Continuous (fun x => A x * curveSpeed F d t x))
    (alpha beta : ℝ) :
    (∫ x in alpha..beta, A (phi x) * curveSpeed F (fun y s => d (phi y) s) t x) =
      ∫ y in phi alpha..phi beta, A y * curveSpeed F d t y := by
  calc
    _ = ∫ x in alpha..beta,
        (A (phi x) * curveSpeed F d t (phi x)) * deriv phi x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [curveSpeed_comp F d (hd (phi x))
        (hphi.differentiable (by norm_num) x).hasDerivAt (hpos x).le]
      ring
    _ = _ := intervalIntegral.integral_comp_mul_deriv
      (fun x _ => (hphi.differentiable (by norm_num) x).hasDerivAt)
      hphi.continuous_deriv_one.continuousOn hA

theorem periodic_density_integral_comp
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ x, 0 < deriv phi x)
    (hshift : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod)
    (A : ℝ → ℝ) (hA : Continuous (fun x => A x * curveSpeed F d t x))
    (hper : Function.Periodic (fun x => A x * curveSpeed F d t x) curvePeriod) :
    (∫ x in (0 : ℝ)..curvePeriod,
      A (phi x) * curveSpeed F (fun y s => d (phi y) s) t x) =
      ∫ y in (0 : ℝ)..curvePeriod, A y * curveSpeed F d t y := by
  calc
    _ = ∫ x in (0 : ℝ)..curvePeriod,
        deriv phi x • (A (phi x) * curveSpeed F d t (phi x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [curveSpeed_comp F d (hd (phi x))
        (hphi.differentiable (by norm_num) x).hasDerivAt (hpos x).le]
      simp only [smul_eq_mul]
      ring
    _ = _ := by
      simpa only [zero_add] using hper.integral_deriv_smul_comp_eq hA hphi hshift 0

theorem arcLength_comp
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hv : Continuous (curveSpeed F d t))
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ x, 0 < deriv phi x) (alpha beta : ℝ) :
    m63ArcLength F (fun y s => d (phi y) s) t alpha beta =
      m63ArcLength F d t (phi alpha) (phi beta) := by
  simpa only [m63ArcLength, one_mul] using
    integral_density_comp F d hd hphi hpos (fun _ => 1) (by simpa using hv) alpha beta

theorem smooth_length_comp (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ x, 0 < deriv phi x)
    (hshift : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod)
    (ht : t ∈ Icc a b) :
    m62Length F (fun y s => d (phi y) s) t = m62Length F d t := by
  have hv : Continuous (curveSpeed F d t) :=
    (M62.speed_continuousOn F d hd).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  simpa only [m62Length, one_mul] using periodic_density_integral_comp F d
    ((hd.spatial_regular t ht).mdifferentiable (by norm_num)) hphi hpos hshift
    (fun _ => 1) (by simpa using hv) (by simpa using M62.speed_periodic F d hd ht)

theorem smooth_arcTotalCurvature_comp (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ x, 0 < deriv phi x)
    (ht : t ∈ Icc a b) (alpha beta : ℝ) :
    m63ArcTotalCurvature F (fun y s => d (phi y) s) t alpha beta =
      m63ArcTotalCurvature F d t (phi alpha) (phi beta) := by
  have hdiff := (hd.spatial_regular t ht).mdifferentiable
    (by norm_num)
  have hk : m62Curvature F (fun y s => d (phi y) s) t =
      fun x => m62Curvature F d t (phi x) := funext fun x =>
    curvature_comp F d hdiff (hphi.differentiable (by norm_num)) hpos
      ((M62.unitTangent_contMDiff F d hd ht (phi x)).mdifferentiableAt (by simp))
  have hcont : Continuous (fun x => m62Curvature F d t x * curveSpeed F d t x) :=
    ((M62.curvature_continuousOn F d hd).mul (M62.speed_continuousOn F d hd)).comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun _ => ⟨mem_univ _, ht⟩)
  unfold m63ArcTotalCurvature
  rw [hk]
  exact integral_density_comp F d hdiff hphi hpos _ hcont alpha beta

theorem smooth_totalCurvature_comp (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ x, 0 < deriv phi x)
    (hshift : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod)
    (ht : t ∈ Icc a b) :
    m62TotalCurvature F (fun y s => d (phi y) s) t = m62TotalCurvature F d t := by
  change m63ArcTotalCurvature F (fun y s => d (phi y) s) t 0 curvePeriod = _
  rw [smooth_arcTotalCurvature_comp F d hd hphi hpos ht 0 curvePeriod]
  have hper : Function.Periodic
      (fun x => m62Curvature F d t x * curveSpeed F d t x) curvePeriod := by
    intro x
    dsimp only
    unfold m62Curvature
    rw [m63CurvatureSquared_periodic F d hd ht x, M62.speed_periodic F d hd ht x]
  have hzero := hshift 0
  rw [zero_add] at hzero
  unfold m63ArcTotalCurvature m62TotalCurvature
  rw [hzero]
  simpa only [zero_add] using hper.intervalIntegral_add_eq (phi 0) 0

theorem smooth_regularizedTotalCurvature_comp (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ x, 0 < deriv phi x)
    (hshift : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod)
    (ht : t ∈ Icc a b) (epsilon : ℝ) :
    m62RegularizedTotalCurvature F (fun y s => d (phi y) s) epsilon t =
      m62RegularizedTotalCurvature F d epsilon t := by
  have hdiff := (hd.spatial_regular t ht).mdifferentiable
    (by norm_num)
  have hk : m62RegularizedCurvature F (fun y s => d (phi y) s) epsilon t =
      fun x => m62RegularizedCurvature F d epsilon t (phi x) := funext fun x =>
    regularizedCurvature_comp F d hdiff (hphi.differentiable (by norm_num)) hpos
      ((M62.unitTangent_contMDiff F d hd ht (phi x)).mdifferentiableAt (by simp)) epsilon
  have hcont : Continuous
      (fun x => m62RegularizedCurvature F d epsilon t x * curveSpeed F d t x) :=
    ((M62.regularized_continuousOn F d hd epsilon).mul
      (M62.speed_continuousOn F d hd)).comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun _ => ⟨mem_univ _, ht⟩)
  have hper : Function.Periodic
      (fun x => m62RegularizedCurvature F d epsilon t x * curveSpeed F d t x)
      curvePeriod := by
    intro x
    dsimp only
    unfold m62RegularizedCurvature
    rw [m63CurvatureSquared_periodic F d hd ht x, M62.speed_periodic F d hd ht x]
  unfold m62RegularizedTotalCurvature
  rw [hk]
  exact periodic_density_integral_comp F d hdiff hphi hpos hshift _ hcont hper

theorem smooth_curvatureEnergy_comp (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ x, 0 < deriv phi x)
    (hshift : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod)
    (ht : t ∈ Icc a b) :
    (∫ x in (0 : ℝ)..curvePeriod,
      m62CurvatureSquared F (fun y s => d (phi y) s) t x *
        curveSpeed F (fun y s => d (phi y) s) t x) =
      ∫ x in (0 : ℝ)..curvePeriod, m62CurvatureSquared F d t x * curveSpeed F d t x := by
  have hdiff := (hd.spatial_regular t ht).mdifferentiable
    (by norm_num)
  have hk : m62CurvatureSquared F (fun y s => d (phi y) s) t =
      fun x => m62CurvatureSquared F d t (phi x) := funext fun x =>
    curvatureSquared_comp F d hdiff (hphi.differentiable (by norm_num)) hpos
      ((M62.unitTangent_contMDiff F d hd ht (phi x)).mdifferentiableAt (by simp))
  have hcont : Continuous (fun x => m62CurvatureSquared F d t x * curveSpeed F d t x) :=
    ((M62.curvatureSquared_continuousOn F d hd).mul
      (M62.speed_continuousOn F d hd)).comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun _ => ⟨mem_univ _, ht⟩)
  have hper : Function.Periodic
      (fun x => m62CurvatureSquared F d t x * curveSpeed F d t x) curvePeriod := by
    intro x
    dsimp only
    rw [m63CurvatureSquared_periodic F d hd ht x, M62.speed_periodic F d hd ht x]
  rw [hk]
  exact periodic_density_integral_comp F d hdiff hphi hpos hshift _ hcont hper

theorem tangentRicci_periodic (hd : M62ShrinkingCurve F d) (ht : t ∈ Icc a b) :
    Function.Periodic (m62TangentRicci F d t) curvePeriod := by
  have hvelocity := m63CurveVelocity_periodic
    ((hd.spatial_regular t ht).mdifferentiable (by norm_num)) (hd.periodic t ht)
  intro x
  have hvel : curveVelocity (fun y => d y t) (x + curvePeriod) =
      curveVelocity (fun y => d y t) x := hvelocity x
  unfold m62TangentRicci spatialUnitTangent
  rw [M62.speed_periodic F d hd ht x, hvel, hd.periodic t ht x]

theorem smooth_lengthEvolutionIntegral_comp (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ x, 0 < deriv phi x)
    (hshift : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod)
    (ht : t ∈ Ioo a b) :
    (∫ x in (0 : ℝ)..curvePeriod,
      (m62CurvatureSquared F (fun y s => d (phi y) s) t x +
        m62TangentRicci F (fun y s => d (phi y) s) t x) *
          curveSpeed F (fun y s => d (phi y) s) t x) =
      ∫ x in (0 : ℝ)..curvePeriod,
        (m62CurvatureSquared F d t x + m62TangentRicci F d t x) * curveSpeed F d t x := by
  have hdiff := (hd.spatial_regular t (Ioo_subset_Icc_self ht)).mdifferentiable
    (by norm_num)
  have hk : m62CurvatureSquared F (fun y s => d (phi y) s) t =
      fun x => m62CurvatureSquared F d t (phi x) := funext fun x =>
    curvatureSquared_comp F d hdiff (hphi.differentiable (by norm_num)) hpos
      (unitTangent_mdifferentiable F d hd ht (phi x))
  have hRic : m62TangentRicci F (fun y s => d (phi y) s) t =
      fun x => m62TangentRicci F d t (phi x) := funext fun x =>
    tangentRicci_comp F d (hdiff (phi x)) (hphi.differentiable (by norm_num) x) (hpos x)
  have hcont : Continuous (fun x =>
      (m62CurvatureSquared F d t x + m62TangentRicci F d t x) * curveSpeed F d t x) := by
    have hcoeff := (M62.normalization_coefficient_contDiffOn F d hd).continuousOn
    have hv := (M62.speed_joint_contDiffOn F d hd).continuousOn
    simpa +instances only [Function.comp_def, Pi.mul_apply, id_eq, add_comm] using!
      (hcoeff.mul hv).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hper : Function.Periodic (fun x =>
      (m62CurvatureSquared F d t x + m62TangentRicci F d t x) * curveSpeed F d t x)
      curvePeriod := by
    intro x
    dsimp only
    rw [M62.curvatureSquared_periodic F d hd ht x,
      tangentRicci_periodic F d hd (Ioo_subset_Icc_self ht) x,
      M62.speed_periodic F d hd (Ioo_subset_Icc_self ht) x]
  rw [hk, hRic]
  exact periodic_density_integral_comp F d hdiff hphi hpos hshift _ hcont hper

end PoincareConjecture.M63
