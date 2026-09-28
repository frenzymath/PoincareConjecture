import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Volume.ModelCaps
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ScaleComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace DeepHorn

def neckNoncollapseConstant : ℝ := modelDiskArea / 512

theorem neckNoncollapseConstant_pos : 0 < neckNoncollapseConstant :=
  div_pos modelDiskArea_pos (by norm_num)

end DeepHorn

namespace EpsilonNeck

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem edist_coordinate_cap_le (q : UnitTwoSphere)
    (x : EuclideanSpace ℝ (Fin 2)) :
    g.edist (N.coordinate_map (q, 0))
      (N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x, 0)) ≤
        ENNReal.ofReal (2 * N.scale * ‖x‖) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let F : EuclideanSpace ℝ (Fin 2) → M := fun y => N.coordinate_map (c.symm y, 0)
  have hz : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hcoord (y : EuclideanSpace ℝ (Fin 2)) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        N.coordinate_map (c.symm y, 0) :=
    N.coordinate_map_smooth.contMDiffAt (N.cylinderDomain_open.mem_nhds ⟨mem_univ _, hz⟩)
  have hF : ContMDiff (𝓡 2) (𝓡 3) 1 F := by
    intro y
    exact ((hcoord y).comp y
      ((sphere_chart_symm_contMDiff q y).prodMk contMDiffAt_const)).of_le (by simp)
  have hd (y v : EuclideanSpace ℝ (Fin 2)) :
      mfderiv (𝓡 2) (𝓡 3) F y v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (c.symm y, 0)
          (mfderiv (𝓡 2) (𝓡 2) c.symm y v, 0) := by
    change mfderiv (𝓡 2) (𝓡 3) (N.coordinate_map ∘ fun y => (c.symm y, 0)) y v = _
    rw [mfderiv_comp_apply y ((hcoord y).mdifferentiableAt (by simp))
      (((sphere_chart_symm_contMDiff q y).mdifferentiableAt (by simp)).prodMk
        mdifferentiableAt_const)]
    rw [mfderiv_prodMk
      ((sphere_chart_symm_contMDiff q y).mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mfderiv_const]
    rfl
  have hbound (y v : EuclideanSpace ℝ (Fin 2)) :
      g.inner (F y) (mfderiv (𝓡 2) (𝓡 3) F y v)
        (mfderiv (𝓡 2) (𝓡 3) F y v) ≤
          (2 * N.scale) ^ 2 * (RiemannianMetric.euclideanMetric 2).inner y v v := by
    have h := (N.pullback_metric_bounds (z := (c.symm y, 0)) hz
      (mfderiv (𝓡 2) (𝓡 2) c.symm y v, 0)).2
    have hround := (roundSphere_chart_quadratic_bounds q (x := y) le_rfl v).2
    change (roundSphereMetric 2).inner (c.symm y)
      (mfderiv (𝓡 2) (𝓡 2) c.symm y v)
      (mfderiv (𝓡 2) (𝓡 2) c.symm y v) ≤ ‖v‖ ^ 2 at hround
    rw [hd]
    change roundCylinderPullback g N.coordinate_map (c.symm y, 0) _ _ ≤ _
    simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one, mul_zero, add_zero] at h
    rw [RiemannianMetric.euclideanMetric_inner, real_inner_self_eq_norm_sq]
    have hcoefficient : (1 + N.epsilon) * N.scale ^ 2 * 2 ≤ (2 * N.scale) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg N.scale) (show 0 ≤ 1 / 2 - N.epsilon by
        linarith [N.epsilon_lt_half])]
    calc
      _ ≤ (1 + N.epsilon) * N.scale ^ 2 * (2 *
          (roundSphereMetric 2).inner (c.symm y)
            (mfderiv (𝓡 2) (𝓡 2) c.symm y v)
            (mfderiv (𝓡 2) (𝓡 2) c.symm y v)) := h
      _ ≤ ((1 + N.epsilon) * N.scale ^ 2 * 2) * ‖v‖ ^ 2 := by
        exact (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hround (by norm_num : (0 : ℝ) ≤ 2))
          (mul_nonneg (by linarith [N.epsilon_pos]) (sq_nonneg _))).trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)
  have hdist := (RiemannianMetric.euclideanMetric 2).edist_le_mul_of_inner_mfderiv_le
    g hF (mul_pos (by norm_num) N.scale_pos) hbound 0 x
  simpa only [F, c, sphere_chart_symm_zero, RiemannianMetric.euclideanMetric_edist,
    edist_dist, dist_zero_left,
    ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) N.scale_pos.le)]
      using hdist

theorem cap_interval_subset_ball (q : UnitTwoSphere) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    N.coordinate_map '' (DeepHorn.modelCap q a ×ˢ Ioo (-a) a) ⊆
      g.ball (N.coordinate_map (q, 0)) (4 * N.scale * a) := by
  have hscale := N.scale_pos
  rintro y ⟨⟨p, t⟩, ⟨⟨x, hx, rfl⟩, ht⟩, rfl⟩
  have hxnorm : ‖x‖ < a := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have htabs : |t| < a := abs_lt.mpr ht
  have hinv : (1 : ℝ) < N.epsilon⁻¹ :=
    (one_lt_inv₀ N.epsilon_pos).mpr (by linarith [N.epsilon_lt_half])
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have htN : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨by linarith [ht.1], ht.2.trans_le (ha1.trans hinv.le)⟩
  have haxis := N.edist_coordinate_map_axis_le
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x) hzero htN
  simp only [sub_zero] at haxis
  have hroot : Real.sqrt (1 + N.epsilon) ≤ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon), N.epsilon_lt_half]
  have haxis' : g.edist
      (N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x, 0))
      (N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x, t)) ≤
        ENNReal.ofReal (2 * N.scale * |t|) := by
    apply haxis.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hroot N.scale_pos.le) (abs_nonneg t)]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change g.edist _ _ < _
  apply (Manifold.riemannianEDist_triangle (y :=
    N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x, 0))).trans_lt
  apply (add_le_add (N.edist_coordinate_cap_le q x) haxis').trans_lt
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 4 * N.scale * a)).mpr
  nlinarith [mul_pos N.scale_pos (sub_pos.mpr hxnorm),
    mul_pos N.scale_pos (sub_pos.mpr htabs)]

theorem volume_center_ball_lower_of_le_two_scale {r : ℝ} (hr : 0 < r)
    (hrscale : r ≤ 2 * N.scale) :
    ENNReal.ofReal (DeepHorn.neckNoncollapseConstant * r ^ 3) ≤
      g.volumeMeasure (g.ball N.center r) := by
  have hscale := N.scale_pos
  have harea := DeepHorn.modelDiskArea_pos
  let a := r / (4 * N.scale)
  have ha : 0 < a := div_pos hr (mul_pos (by norm_num) N.scale_pos)
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) N.scale_pos)).mpr
    linarith [N.scale_pos]
  have har : 4 * N.scale * a = r := by
    dsimp [a]
    field_simp [N.scale_pos.ne']
  obtain ⟨⟨q, s⟩, ⟨_, hs⟩, hcenter⟩ := N.central_sphere_eq ▸ N.center_on_central_sphere
  have hs0 : s = 0 := hs
  subst s
  let A := DeepHorn.modelCap q a ×ˢ Ioo (-a) a
  have hA : MeasurableSet A := (DeepHorn.modelCap_open q a).measurableSet.prod measurableSet_Ioo
  have hinv : (1 : ℝ) < N.epsilon⁻¹ :=
    (one_lt_inv₀ N.epsilon_pos).mpr (by linarith [N.epsilon_lt_half])
  have hAN : A ⊆ N.cylinderDomain := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    exact ⟨mem_univ _, by linarith [ht.1], ht.2.trans_le (ha1.trans hinv.le)⟩
  have hAball : N.coordinate_map '' A ⊆ g.ball N.center r := by
    simpa only [hcenter, har, A] using N.cap_interval_subset_ball q ha ha1
  have hline : volume (Ioo (-a) a) = ENNReal.ofReal (2 * a) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hmodel : ENNReal.ofReal (DeepHorn.modelDiskArea * a ^ 3) ≤
      roundCylinderVolumeMeasure A := by
    rw [roundCylinderVolumeMeasure_eq_prod, Measure.prod_prod, hline]
    have hrewrite : ENNReal.ofReal (DeepHorn.modelDiskArea * a ^ 3) =
        ENNReal.ofReal (DeepHorn.modelDiskArea * a ^ 2 / 2) * ENNReal.ofReal (2 * a) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ DeepHorn.modelDiskArea * a ^ 2 / 2)]
      congr 1
      ring
    rw [hrewrite]
    exact mul_le_mul' (DeepHorn.modelCap_area_lower q ha ha1) le_rfl
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
    nlinarith [N.epsilon_lt_half, Real.sqrt_nonneg (1 - N.epsilon)]
  have hfactor : N.scale / 2 ≤ N.scale * Real.sqrt (1 - N.epsilon) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hroot N.scale_pos.le
  have hrewrite : ENNReal.ofReal (DeepHorn.neckNoncollapseConstant * r ^ 3) =
      ENNReal.ofReal (N.scale / 2) ^ 3 *
        ENNReal.ofReal (DeepHorn.modelDiskArea * a ^ 3) := by
    rw [← ENNReal.ofReal_pow (div_nonneg N.scale_pos.le (by norm_num)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (N.scale / 2) ^ 3)]
    congr 1
    dsimp [a, DeepHorn.neckNoncollapseConstant]
    field_simp [N.scale_pos.ne']
    ring
  rw [hrewrite]
  apply le_trans _ ((N.volumeMeasure_image_bounds hA hAN).1.trans (measure_mono hAball))
  gcongr

end EpsilonNeck

namespace GeneralizedStrongNeck

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}

theorem radius_le_two_scale_of_curvature_bound (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) {r : ℝ} (hr : 0 < r)
    (hcurv : |F.curvatureNorm ⟨t, N.center⟩| ≤ r⁻¹ ^ 2) :
    r ≤ 2 * N.scale := by
  have hscalar := (F.connection t).scalarCurvature_le_curvatureTensorNorm_sharp N.center
  have hR : (F.connection t).scalarCurvature N.center ≤ 3 * r⁻¹ ^ 2 := by
    exact hscalar.trans (by
      norm_num only [Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcurv) (by norm_num))
  have hnorm := (N.spatialNeck hepsilon).scale_sq_mul_scalar_center
  change N.scale ^ 2 * (F.connection t).scalarCurvature N.center = 1 at hnorm
  have hm := mul_le_mul_of_nonneg_left hR (sq_nonneg r)
  have hcancel : r ^ 2 * (3 * r⁻¹ ^ 2) = 3 := by field_simp
  rw [hcancel] at hm
  have hm' := mul_le_mul_of_nonneg_left hm (sq_nonneg N.scale)
  have hprod : N.scale ^ 2 * (r ^ 2 * (F.connection t).scalarCurvature N.center) = r ^ 2 := by
    calc
      _ = r ^ 2 * (N.scale ^ 2 * (F.connection t).scalarCurvature N.center) := by ring
      _ = r ^ 2 := by rw [hnorm, mul_one]
  rw [hprod] at hm'
  nlinarith [N.scale_pos]

theorem noncollapsed_at_center (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) (r₀ : ℝ) :
    GeneralizedKappaNoncollapsedAt F ⟨t, N.center⟩
      DeepHorn.neckNoncollapseConstant r₀ := by
  intro r hr _ _ e hidentity hcurv
  have hzero : (0 : ℝ) ∈ Ioc (-r ^ 2) 0 := ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩
  have hcenter : N.center ∈ (F.metric t).ball N.center r := by
    change (F.metric t).edist N.center N.center < ENNReal.ofReal r
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hr
  have htop := hcurv 0 hzero N.center hcenter
  rw [hidentity hzero N.center hcenter] at htop
  have hrscale := N.radius_le_two_scale_of_curvature_bound hepsilon hr htop
  have hv := (N.spatialNeck hepsilon).volume_center_ball_lower_of_le_two_scale hr hrscale
  rw [Generalized.Noncollapse.calibratedMetricVolume_eq_euclideanHausdorff]
  exact hv

end GeneralizedStrongNeck

end PoincareConjecture
