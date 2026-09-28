import PoincareConjecture.Proofs.M30.Generalized.RecenteredCylinder
import PoincareConjecture.Proofs.M30.Generalized.PhysicalClock
import PoincareConjecture.Proofs.M13.Volume

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M30.Cylinder

theorem normalized_volume_of_recentered_noncollapse
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {a q : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C a q J.domain U)
    (t0 : J.domain) (p : (F.slice (a + t0.val / q)).carrier)
    {rho kappa r0 : ℝ} (hrho : 0 < rho)
    (hcutoff : rho / Real.sqrt q ≤ r0)
    (htime : Icc (-rho ^ 2) 0 ⊆
      (fun s : ℝ => t0.val + s) ⁻¹' J.domain)
    (hnon : GeneralizedKappaNoncollapsedAt F
      (⟨a + t0.val / q, p⟩ : F.point) kappa r0) :
    let h : RiemannianMetric 3 (F.slice (a + t0.val / q)).carrier :=
      M13.scaleSmoothMetric (F.metric (a + t0.val / q)) q e.scale_pos
    h.ball p rho ⊆ e.forward t0.val t0.property '' (U : Set C.carrier) →
    (∀ s (hs : s ∈ Ioc (-rho ^ 2) 0), ∀ y ∈ h.ball p rho,
      |F.curvatureNorm (e.pointMap (t0.val + s)
        (htime (Ioc_subset_Icc_self hs)) (e.inverse t0.val t0.property y))| / q ≤
          rho⁻¹ ^ 2) →
    ENNReal.ofReal (kappa * rho ^ 3) ≤
      calibratedMetricVolume h (h.ball p rho) := by
  intro h hball hcurv
  let b := a + t0.val / q
  let X := (F.slice b).carrier
  let g : RiemannianMetric 3 X := F.metric b
  let r := rho / Real.sqrt q
  have hq : 0 < q := e.scale_pos
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hr : 0 < r := div_pos hrho hsqrt
  have hqr : q * r ^ 2 = rho ^ 2 := by
    dsimp only [r]
    rw [div_pow, Real.sq_sqrt hq.le, mul_div_cancel₀ _ hq.ne']
  have hhom : MetricHomothety g h (Diffeomorph.refl (𝓡 3) X ∞) q := by
    intro x v w
    rw [Diffeomorph.coe_refl]
    change h.inner x (mfderiv (𝓡 3) (𝓡 3) (@id X) x v)
      (mfderiv (𝓡 3) (𝓡 3) (@id X) x w) = q * g.inner x v w
    rw [mfderiv_id]
    rfl
  have hballEq : g.ball p r = h.ball p rho := by
    have H := M13.homothety_ball_image g h (Diffeomorph.refl (𝓡 3) X ∞)
      q hq hhom p r
    simpa only [Diffeomorph.coe_refl, image_id, id_eq, r,
      mul_div_cancel₀ _ hsqrt.ne'] using H
  have hopen : IsOpen (g.ball p r) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : X → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace X := EMetricSpace.ofRiemannianMetric (𝓡 3) X
    change IsOpen {y : X | edist p y < ENNReal.ofReal r}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let V : TopologicalSpace.Opens X := ⟨g.ball p r, hopen⟩
  have hV : (V : Set X) ⊆ e.forward t0.val t0.property '' (U : Set C.carrier) := by
    change g.ball p r ⊆ _
    rwa [hballEq]
  let er := recenter e t0 V hV htime
  have hclock (s : ℝ) (hs : s ∈ Ioc (-r ^ 2) 0) :
      q * s ∈ Ioc (-rho ^ 2) 0 := by
    constructor
    · have H := mul_lt_mul_of_pos_left hs.1 hq
      nlinarith only [H, hqr]
    · exact mul_nonpos_of_nonneg_of_nonpos hq.le hs.2
  have hclockClosed : Ioc (-r ^ 2) 0 ⊆
      (fun s : ℝ => q * s) ⁻¹' Icc (-rho ^ 2) 0 :=
    fun s hs => Ioc_subset_Icc_self (hclock s hs)
  let ep := physicalTime er hclockClosed
  have hpoints (s : ℝ) (hs : s ∈ Ioc (-r ^ 2) 0) (y : X) :
      ep.pointMap s hs y = e.pointMap (t0.val + q * s)
        (htime (Ioc_subset_Icc_self (hclock s hs))) (e.inverse t0.val t0.property y) := by
    rw [physicalTime_pointMap, recenter_pointMap]
  have hinterval : Ioc (b - r ^ 2) b ⊆ F.interval := by
    intro t ht
    have hs : t - b ∈ Ioc (-r ^ 2) 0 := by constructor <;> linarith [ht.1, ht.2]
    have H := (F.slice_nonempty_iff _).mp ⟨ep.forward (t - b) hs p⟩
    have heq : b + (t - b) / 1 = t := by ring
    rwa [heq] at H
  have hzero (h0 : (0 : ℝ) ∈ Ioc (-r ^ 2) 0) (y : X) (hy : y ∈ g.ball p r) :
      ep.pointMap 0 h0 y = (⟨b, y⟩ : F.point) := by
    rw [physicalTime_pointMap]
    have H := recenter_zero_identity e t0 V hV htime
      (show (0 : ℝ) ∈ Icc (-rho ^ 2) 0 from ⟨neg_nonpos.mpr (sq_nonneg rho), le_rfl⟩)
      y hy
    simpa only [mul_zero] using H
  have hscale : rho⁻¹ ^ 2 * q = r⁻¹ ^ 2 := by
    rw [inv_pow, inv_pow, inv_eq_one_div, inv_eq_one_div]
    apply (eq_div_iff (pow_ne_zero 2 hr.ne')).mpr
    rw [mul_assoc, hqr, one_div_mul_cancel (pow_ne_zero 2 hrho.ne')]
  have hphysical (s : ℝ) (hs : s ∈ Ioc (-r ^ 2) 0) (y : X)
      (hy : y ∈ g.ball p r) : |F.curvatureNorm (ep.pointMap s hs y)| ≤ r⁻¹ ^ 2 := by
    rw [hpoints]
    have H := (div_le_iff₀ hq).mp (hcurv (q * s) (hclock s hs) y (hballEq ▸ hy))
    exact H.trans_eq hscale
  have hsource := hnon r hr hcutoff hinterval ep hzero hphysical
  have hvolume := M13.homothety_volume_image g h (Diffeomorph.refl (𝓡 3) X ∞)
    q hq hhom (g.ball p r)
  simp only [Diffeomorph.coe_refl, image_id] at hvolume
  rw [hballEq] at hvolume hsource
  have hfactor : Real.rpow q ((3 : ℝ) / 2) = Real.sqrt q ^ 3 := by
    rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt (3 : ℝ) hq.le]
    norm_num
  have hvolume' : calibratedMetricVolume h (h.ball p rho) =
      ENNReal.ofReal (Real.sqrt q ^ 3) * calibratedMetricVolume g (h.ball p rho) := by
    convert hvolume using 1
    exact congrArg (fun z : ℝ≥0∞ => z * calibratedMetricVolume g (h.ball p rho))
      (congrArg ENNReal.ofReal hfactor).symm
  rw [hvolume']
  have heq : ENNReal.ofReal (kappa * rho ^ 3) = ENNReal.ofReal (Real.sqrt q ^ 3) *
      ENNReal.ofReal (kappa * r ^ 3) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hsqrt.le 3)]
    congr 1
    dsimp only [r]
    field_simp
  rw [heq]
  exact mul_le_mul_right hsource _

end PoincareConjecture.M30.Cylinder
