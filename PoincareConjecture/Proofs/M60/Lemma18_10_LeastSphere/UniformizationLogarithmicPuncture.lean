import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationFlatDevelopment
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationSphereCurvature
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationFlattening
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationPoissonClosed
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUConformalPole
import PoincareConjecture.Proofs.M60.Mathlib.SupportedChartExtension
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundLaplacian
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactDerivative
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle
noncomputable section
namespace PoincareConjecture.M60
private abbrev Plane := EuclideanSpace ℝ (Fin 2)
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem cutoff_square_hasCompactSupport (chi : ContDiffBump (0 : ℝ))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] :
    HasCompactSupport (fun x : E => chi (‖x‖ ^ 2)) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E) (chi.rOut + 1))
  intro x hx
  have hn : chi.rOut + 1 < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hx
  apply chi.zero_of_le_dist
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [chi.rOut_pos]

theorem radial_cutoff_source (chi : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ∞ (fun x : Plane => 2 * deriv chi (‖x‖ ^ 2)) ∧
      HasCompactSupport (fun x : Plane => 2 * deriv chi (‖x‖ ^ 2)) ∧
      Integrable (fun x : Plane => 2 * deriv chi (‖x‖ ^ 2)) ∧
      (∫ x : Plane, 2 * deriv chi (‖x‖ ^ 2)) = -2 * Real.pi := by
  have hchi : ContDiff ℝ ∞ chi := chi.contDiff
  have hdchi : ContDiff ℝ ∞ (deriv chi) := hchi.deriv'
  have hs : ContDiff ℝ ∞ (fun x : Plane => 2 * deriv chi (‖x‖ ^ 2)) :=
    contDiff_const.mul (hdchi.comp (contDiff_norm_sq ℝ))
  have hc : HasCompactSupport (fun x : Plane => 2 * deriv chi (‖x‖ ^ 2)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Plane) (chi.rOut + 1))
    intro x hx
    have hn : chi.rOut + 1 < ‖x‖ := by
      simpa only [mem_closedBall_zero_iff, not_le] using hx
    have hts : ‖x‖ ^ 2 ∉ tsupport (chi : ℝ → ℝ) := by
      rw [chi.tsupport_eq, mem_closedBall_zero_iff]
      simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖), not_le]
      nlinarith [chi.rOut_pos]
    rw [deriv_of_notMem_tsupport hts, mul_zero]
  refine ⟨hs, hc, hs.continuous.integrable_of_hasCompactSupport hc, ?_⟩
  let Q : ℝ → ℝ := fun r => chi (r ^ 2)
  have hQ : ContDiff ℝ ∞ Q := chi.contDiff.comp (contDiff_id.pow 2)
  have hQc : HasCompactSupport Q := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (cutoff_square_hasCompactSupport chi (E := ℝ))
  have hdQ (r : ℝ) : deriv Q r = r * (2 * deriv chi (r ^ 2)) := by
    have h := ((hchi.differentiable (by simp)) (r ^ 2)).hasDerivAt.comp r
      ((hasDerivAt_id r).pow 2)
    convert! h.deriv using 1
    simp only [id_eq]
    ring
  have hrad : (∫ r in Ioi (0 : ℝ), r * (2 * deriv chi (r ^ 2))) = -1 := by
    simp_rw [← hdQ]
    rw [hQc.integral_Ioi_deriv_eq (hQ.of_le (by simp))]
    have hchi0 : chi 0 = 1 := chi.one_of_mem_closedBall (by simp [chi.rIn_pos.le])
    simp only [Q, zero_pow (by decide : (2 : ℕ) ≠ 0), hchi0]
  rw [← Proofs.M58.integral_polar_loopPlane, polarCoord_target]
  calc
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 * (2 * deriv chi (p.1 ^ 2))) * (1 : ℝ) := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hr : 0 < p.1 := hp.1
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        Proofs.M58.norm_angularPoint, mul_one]
    _ = (∫ r in Ioi (0 : ℝ), r * (2 * deriv chi (r ^ 2))) *
        (∫ t in Ioo (-Real.pi) Real.pi, (1 : ℝ)) := by
      change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 * (2 * deriv chi (p.1 ^ 2))) * (1 : ℝ) ∂volume.prod volume) = _
      exact setIntegral_prod_mul (fun r : ℝ => r * (2 * deriv chi (r ^ 2)))
        (fun _ : ℝ => 1) (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi)
    _ = -2 * Real.pi := by
      rw [hrad]
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi),
        smul_eq_mul, mul_one]
      ring

theorem exists_radial_logarithmic_potential (chi : ContDiffBump (0 : ℝ)) :
    ∃ A J : Plane → ℝ, ContDiff ℝ ∞ J ∧
      (∀ x ≠ 0, A x = Real.log ‖x‖ + J x) ∧
      (∀ x, chi.rOut < ‖x‖ ^ 2 → A x = 0) ∧
      (∀ x ≠ 0, ContDiffAt ℝ ∞ A x) ∧
      (∀ x ≠ 0, ∀ v, fderiv ℝ A x v =
        (chi (‖x‖ ^ 2) / ‖x‖ ^ 2) * inner ℝ x v) := by
  let b : ℝ → ℝ := fun t => (chi t - 1) / (2 * t)
  have hb : ContDiff ℝ ∞ b := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    by_cases ht : t = 0
    · subst t
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [chi.eventuallyEq_one] with s hs
      simp [b, hs]
    · exact (chi.contDiff.contDiffAt.sub contDiffAt_const).div
        (contDiffAt_const.mul contDiffAt_id) (mul_ne_zero (by norm_num) ht)
  let B : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, b s
  have hBder (t : ℝ) : HasDerivAt B (b t) t :=
    (hb.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hB : ContDiff ℝ ∞ B := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨fun t => (hBder t).differentiableAt,
      (show deriv B = b from funext fun t => (hBder t).deriv) ▸ hb⟩
  let H : ℝ → ℝ := fun t => Real.log t / 2 + B t
  have hHd (t : ℝ) (ht : 0 < t) : HasDerivAt H (chi t / (2 * t)) t := by
    have h := ((Real.hasDerivAt_log ht.ne').div_const 2).add (hBder t)
    convert! h using 1
    dsimp [b]
    field_simp
    ring
  have hHs (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ ∞ H t :=
    ((contDiffAt_id.log ht.ne').div_const 2).add hB.contDiffAt
  let A : Plane → ℝ := fun x => H (‖x‖ ^ 2) - H chi.rOut
  let J : Plane → ℝ := fun x => B (‖x‖ ^ 2) - H chi.rOut
  have hJ : ContDiff ℝ ∞ J := (hB.comp (contDiff_norm_sq ℝ)).sub contDiff_const
  have hAs (x : Plane) (hx : x ≠ 0) : ContDiffAt ℝ ∞ A x :=
    ((hHs (‖x‖ ^ 2) (sq_pos_of_pos (norm_pos_iff.mpr hx))).comp x
      (contDiff_norm_sq ℝ).contDiffAt).sub contDiffAt_const
  have hAd (x : Plane) (hx : x ≠ 0) (v : Plane) :
      fderiv ℝ A x v = (chi (‖x‖ ^ 2) / ‖x‖ ^ 2) * inner ℝ x v := by
    have h := ((hHd (‖x‖ ^ 2) (sq_pos_of_pos (norm_pos_iff.mpr hx))).comp_hasFDerivAt x
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt).sub_const (H chi.rOut)
    change HasFDerivAt A _ x at h
    rw [h.fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  refine ⟨A, J, hJ, fun x hx => ?_, fun x hx => ?_, hAs, hAd⟩
  · dsimp [A, H, J]
    rw [Real.log_pow]
    ring
  · have hconst : ∀ t, chi.rOut ≤ t →
        deriv H t = 0 := by
      intro t htR
      rw [(hHd t (by linarith [chi.rOut_pos])).deriv]
      rw [chi.zero_of_le_dist (by
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by linarith [chi.rOut_pos])]
        exact htR), zero_div]
    have heq := (convex_Ici chi.rOut).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hHd t (lt_of_lt_of_le chi.rOut_pos ht)).differentiableAt)
      (fun t ht => by rw [hconst t ht, norm_zero]) (self_mem_Ici (a := chi.rOut)) hx.le
    change H (‖x‖ ^ 2) - H chi.rOut = 0
    exact norm_le_zero_iff.mp (by simpa only [zero_mul] using heq)

theorem radial_logarithmic_potential_laplacian
    (chi : ContDiffBump (0 : ℝ)) {A : Plane → ℝ}
    (hA : ∀ x ≠ 0, ∀ v, fderiv ℝ A x v =
      (chi (‖x‖ ^ 2) / ‖x‖ ^ 2) * inner ℝ x v)
    {x : Plane} (hx : x ≠ 0) :
    (∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ A y
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 2 * deriv chi (‖x‖ ^ 2) := by
  let t := ‖x‖ ^ 2
  have ht : t ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hchi : ContDiff ℝ ∞ chi := chi.contDiff
  have hd (v : Plane) : fderiv ℝ (fun y => fderiv ℝ A y v) x v =
      (2 * (deriv chi t * t - chi t) / t ^ 2) * (inner ℝ x v) ^ 2 +
        (chi t / t) * ‖v‖ ^ 2 := by
    have heq : (fun y => fderiv ℝ A y v) =ᶠ[𝓝 x]
        (fun y => (chi (‖y‖ ^ 2) / ‖y‖ ^ 2) * inner ℝ y v) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
      exact hA y hy v
    have h1 := (((hchi.differentiable (by simp)) t).hasDerivAt.div
      (hasDerivAt_id t) ht).comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have h2 : HasFDerivAt (fun y : Plane => inner ℝ y v) (innerSL ℝ v) x := by
      convert! (innerSL ℝ v).hasFDerivAt using 1
      ext y
      exact (real_inner_comm y v).symm
    have h := h1.mul h2
    change HasFDerivAt (fun y => (chi (‖y‖ ^ 2) / ‖y‖ ^ 2) * inner ℝ y v) _ x at h
    rw [heq.fderiv_eq, h.fderiv]
    simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
      real_inner_self_eq_norm_sq, Function.comp_def, Pi.div_apply, id_eq, mul_one]
    dsimp only [t]
    ring
  simp only [Fin.sum_univ_two, hd, OrthonormalBasis.norm_eq_one, one_pow]
  have hs : (inner ℝ x (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ^ 2 +
      (inner ℝ x (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ^ 2 = t := by
    simpa only [Fin.sum_univ_two, real_inner_comm] using
      (EuclideanSpace.basisFun (Fin 2) ℝ).sum_sq_inner_right x
  change _ = 2 * deriv chi t
  field_simp
  linear_combination 2 * (deriv chi t * t - chi t) * hs

theorem exists_flat_chart_logarithmic_puncture
    (g : RiemannianMetric 2 UnitTwoSphere) (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph Plane UnitTwoSphere)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hmetric : ∀ x ∈ e.source, ∀ v w : Plane,
      g.pullbackCoefficients e x v w = inner ℝ v w)
    (a : Plane) (ha : a ∈ e.source) :
    ∃ V C : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ C ∧
      (∫ p, C p ∂g.volumeMeasure) = -2 * Real.pi ∧
      (∀ p ≠ e a, ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ V p) ∧
      (∀ p ≠ e a, D.laplacian V p = C p) ∧
      ∃ J : Plane → ℝ, ContDiff ℝ ∞ J ∧
        ∀ x ∈ e.source, x ≠ a → V (e x) = Real.log ‖x - a‖ + J (x - a) := by
  classical
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_source.mem_nhds ha)
  let chi : ContDiffBump (0 : ℝ) :=
    ⟨r ^ 2 / 2, r ^ 2, half_pos (sq_pos_of_pos hr), half_lt_self (sq_pos_of_pos hr)⟩
  obtain ⟨A, J, hJ, hlog, hAzero, hAs, hAd⟩ := exists_radial_logarithmic_potential chi
  obtain ⟨hCs, _, _, hCint⟩ := radial_cutoff_source chi
  let A0 : Plane → ℝ := fun x => A (x - a)
  let C0 : Plane → ℝ := fun x => 2 * deriv chi (‖x - a‖ ^ 2)
  have hA0zero (x : Plane) (hx : x ∉ Metric.closedBall a r) : A0 x = 0 := by
    have hn : r < ‖x - a‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hx
    exact hAzero (x - a) (by change r ^ 2 < ‖x - a‖ ^ 2; nlinarith)
  have hC0zero (x : Plane) (hx : x ∉ Metric.closedBall a r) : C0 x = 0 := by
    have hn : r < ‖x - a‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hx
    have hts : ‖x - a‖ ^ 2 ∉ tsupport (chi : ℝ → ℝ) := by
      rw [chi.tsupport_eq, mem_closedBall_zero_iff]
      simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x - a‖), not_le]
      change r ^ 2 < ‖x - a‖ ^ 2
      nlinarith
    exact mul_eq_zero_of_right 2 (deriv_of_notMem_tsupport hts)
  have hA0supp : tsupport A0 ⊆ Metric.closedBall a r :=
    closure_minimal (by intro x hx; by_contra hn; exact hx (hA0zero x hn))
      Metric.isClosed_closedBall
  have hC0supp : tsupport C0 ⊆ Metric.closedBall a r :=
    closure_minimal (by intro x hx; by_contra hn; exact hx (hC0zero x hn))
      Metric.isClosed_closedBall
  have hA0c : HasCompactSupport A0 := HasCompactSupport.intro (isCompact_closedBall a r) hA0zero
  have hC0c : HasCompactSupport C0 := HasCompactSupport.intro (isCompact_closedBall a r) hC0zero
  have hC0s : ContDiff ℝ ∞ C0 := hCs.comp (contDiff_id.sub contDiff_const)
  let V := supportedChartExtension e.symm A0
  let C := supportedChartExtension e.symm C0
  have hC : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ C :=
    contMDiff_supportedChartExtension e.symm hei hC0s hC0c (hC0supp.trans hrsub)
  have hVout (p : UnitTwoSphere) (hp : p ∉ e.target) : p ∉ tsupport V := by
    intro h
    obtain ⟨x, hx, hxp⟩ := tsupport_supportedChartExtension_subset e.symm hA0c
      (hA0supp.trans hrsub) h
    exact hp (hxp ▸ e.map_source (hrsub (hA0supp hx)))
  have hVc (x : Plane) (hx : x ∈ e.source) : V (e x) = A0 x := by
    change supportedChartExtension e.symm A0 (e x) = A0 x
    rw [supportedChartExtension_of_mem e.symm A0 (e.map_source hx), e.left_inv hx]
  have hCc (x : Plane) (hx : x ∈ e.source) : C (e x) = C0 x := by
    change supportedChartExtension e.symm C0 (e x) = C0 x
    rw [supportedChartExtension_of_mem e.symm C0 (e.map_source hx), e.left_inv hx]
  have hV (p : UnitTwoSphere) (hp : p ≠ e a) :
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ V p := by
    by_cases hpe : p ∈ e.target
    · have hpa : e.symm p - a ≠ 0 := by
        intro h
        exact hp ((e.right_inv hpe).symm.trans (congrArg e (sub_eq_zero.mp h)))
      have hs : ContDiffAt ℝ ∞ A0 (e.symm p) :=
        (hAs _ hpa).comp (e.symm p)
          (show ContDiffAt ℝ ∞ (fun x : Plane => x - a) (e.symm p) from
            contDiffAt_id.sub contDiffAt_const)
      apply ((contMDiffAt_iff_contDiffAt.mpr hs).comp p
        (hei.contMDiffAt (e.open_target.mem_nhds hpe))).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hpe] with q hq
      exact supportedChartExtension_of_mem e.symm A0 hq
    · exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp (hVout p hpe))
  have hden (x : Plane) (hx : x ∈ e.source) : g.pullbackVolumeDensity e x = 1 := by
    unfold RiemannianMetric.pullbackVolumeDensity
    have hm : (Matrix.of fun i j : Fin 2 => g.inner (e x)
        (mfderiv (𝓡 2) (𝓡 2) e x (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 2) e x (EuclideanSpace.basisFun (Fin 2) ℝ j))) =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      change g.pullbackCoefficients e x _ _ = _
      rw [hmetric x hx]
      simpa only [Matrix.one_apply] using
        (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_ite i j
    rw [hm]
    simp
  have hint : (∫ p, C p ∂g.volumeMeasure) = -2 * Real.pi := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target)
      (fun p hp => by simp [C, supportedChartExtension, hp])]
    rw [g.integral_target_eq_integral_pullback_density e he hei hC.continuous.continuousOn]
    calc
      _ = ∫ x in e.source, C0 x := setIntegral_congr_fun e.open_source.measurableSet
        (fun x hx => by rw [hCc x hx, hden x hx, mul_one])
      _ = ∫ x, C0 x := setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hC0zero x (fun hn => hx (hrsub hn)))
      _ = -2 * Real.pi := by
        exact (integral_sub_right_eq_self
          (fun z : Plane => 2 * deriv chi (‖z‖ ^ 2)) a).trans hCint
  let G := RiemannianMetric.euclideanMetric 2
  let DE : LeviCivitaData G := G.euclideanLeviCivitaData
  have hA_lap (x : Plane) (hx : x ≠ 0) : DE.laplacian A x = 2 * deriv chi (‖x‖ ^ 2) := by
    rw [DE.laplacian_euclideanMetric (hAs x hx)]
    rw [← radial_logarithmic_potential_laplacian chi hAd hx]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_clm_apply (((hAs x hx).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)) (differentiableAt_const _)]
    simp
  have hshift (x : Plane) : HasFDerivAt (fun y : Plane => y - a)
      (ContinuousLinearMap.id ℝ Plane) x := (hasFDerivAt_id x).sub_const a
  have hA0lap (x : Plane) (hx : x ≠ a) : DE.laplacian A0 x = C0 x := by
    have h := DE.laplacian_comp_of_metric_pullback DE
      (show ContMDiffAt (𝓡 2) (𝓡 2) ∞ (fun y : Plane => y - a) x from
        contMDiffAt_iff_contDiffAt.mpr (contDiffAt_id.sub contDiffAt_const))
      (Eventually.of_forall (fun y => by
        rw [mfderiv_eq_fderiv, (hshift y).fderiv]
        exact ⟨ContinuousLinearEquiv.refl ℝ Plane, rfl⟩))
      (Eventually.of_forall (fun y v w => by
        rw [mfderiv_eq_fderiv, (hshift y).fderiv]
        rfl)) (contMDiffAt_iff_contDiffAt.mpr (hAs (x - a) (sub_ne_zero.mpr hx)))
    exact h.trans (hA_lap (x - a) (sub_ne_zero.mpr hx))
  have hlap (p : UnitTwoSphere) (hp : p ≠ e a) : D.laplacian V p = C p := by
    by_cases hpe : p ∈ e.target
    · let x := e.symm p
      have hx : x ∈ e.source := e.map_target hpe
      have hxa : x ≠ a := by
        intro h
        exact hp ((e.right_inv hpe).symm.trans (congrArg e h))
      have hdiff : e.MDifferentiable (𝓡 2) (𝓡 2) :=
        ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
      have h := DE.laplacian_comp_of_metric_pullback D
        (he.contMDiffAt (e.open_source.mem_nhds hx))
        (by filter_upwards [e.open_source.mem_nhds hx] with y hy; exact ⟨hdiff.mfderiv hy, rfl⟩)
        (by filter_upwards [e.open_source.mem_nhds hx] with y hy; intro v w;
            exact (hmetric y hy v w).symm)
        (hV (e x) (by rwa [e.right_inv hpe]))
      have heq : V ∘ e =ᶠ[𝓝 x] A0 := by
        filter_upwards [e.open_source.mem_nhds hx] with y hy
        exact hVc y hy
      rw [DE.laplacian_eq_of_eventuallyEq heq, hA0lap x hxa] at h
      rw [← e.right_inv hpe, hCc x hx]
      exact h.symm
    · rw [D.laplacian_eq_zero_of_notMem_tsupport (hVout p hpe)]
      simp [C, supportedChartExtension, hpe]
  refine ⟨V, C, hC, hint, hV, hlap, J, hJ, ?_⟩
  intro x hx hxa
  rw [hVc x hx]
  exact hlog (x - a) (sub_ne_zero.mpr hxa)
end PoincareConjecture.M60

end
