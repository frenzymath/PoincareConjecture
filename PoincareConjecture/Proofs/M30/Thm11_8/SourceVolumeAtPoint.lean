import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSlabControlled
import PoincareConjecture.Proofs.M30.Generalized.PhysicalClock
import PoincareConjecture.Proofs.M30.Generalized.TerminalMetric
import PoincareConjecture.Proofs.M13.Volume

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

private theorem physical_center_volume_bound
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ}
    {A T B eta kappa r₀ rho : ℝ}
    (E : ControlledBlowupCylinder S k A T B eta)
    {x : ((S.flow k).slice (S.base k).1).carrier}
    (hnon : GeneralizedKappaNoncollapsedAt (S.flow k)
      (⟨(S.base k).1, x⟩ : (S.flow k).point) kappa r₀)
    (hrho : 0 < rho) (hT : rho ^ 2 ≤ T) (hB : B * rho ^ 2 ≤ 1)
    (hcutoff : rho / Real.sqrt (S.scale k) ≤ r₀)
    (hball_source : ((S.flow k).metric (S.base k).1).ball x
      (rho / Real.sqrt (S.scale k)) ⊆ S.baseBall k A) :
    ENNReal.ofReal (kappa * (rho / Real.sqrt (S.scale k)) ^ 3) ≤
      calibratedMetricVolume ((S.flow k).metric (S.base k).1)
        (((S.flow k).metric (S.base k).1).ball x
          (rho / Real.sqrt (S.scale k))) := by
  let Q := S.scale k
  let r := rho / Real.sqrt Q
  have hQ : 0 < Q := S.base_scalar_pos k
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hr : 0 < r := div_pos hrho hsqrt
  have hQr : Q * r ^ 2 = rho ^ 2 := by
    dsimp only [r]
    rw [div_pow, Real.sq_sqrt hQ.le, mul_div_cancel₀ _ hQ.ne']
  have hclock : Icc (-r ^ 2) 0 ⊆
      (fun s : ℝ => Q * s) ⁻¹' Icc (-T) 0 := by
    intro s hs
    constructor
    · have h := mul_le_mul_of_nonneg_left hs.1 hQ.le
      nlinarith [hQr]
    · exact mul_nonpos_of_nonneg_of_nonpos hQ.le hs.2
  let ep := Cylinder.physicalTime E.embedding hclock
  let etest : GeneralizedFlowCylinder (S.flow k)
      ((S.flow k).slice (S.base k).1) (S.base k).1 1
      (Ioc (-r ^ 2) 0)
      (((S.flow k).metric (S.base k).1).ball x r) :=
    Cylinder.restrict ep Ioc_subset_Icc_self hball_source
  have hpoints (s : ℝ) (hs : s ∈ Ioc (-r ^ 2) 0)
      (y : ((S.flow k).slice (S.base k).1).carrier) :
      etest.pointMap s hs y =
        E.embedding.pointMap (Q * s) (hclock (Ioc_subset_Icc_self hs)) y :=
    Cylinder.physicalTime_pointMap E.embedding hclock s
      (Ioc_subset_Icc_self hs) y
  have hinterval : Ioc ((S.base k).1 - r ^ 2) (S.base k).1 ⊆
      (S.flow k).interval := by
    intro t ht
    have hs : t - (S.base k).1 ∈ Icc (-r ^ 2) 0 := by
      constructor <;> linarith [ht.1, ht.2]
    have h := ((S.flow k).slice_nonempty_iff _).mp
      ⟨ep.forward (t - (S.base k).1) hs x⟩
    have heq : (S.base k).1 + (t - (S.base k).1) / 1 = t := by ring
    rwa [heq] at h
  have hzero (h₀ : (0 : ℝ) ∈ Ioc (-r ^ 2) 0)
      (y : ((S.flow k).slice (S.base k).1).carrier)
      (hy : y ∈ ((S.flow k).metric (S.base k).1).ball x r) :
      etest.pointMap 0 h₀ y = (⟨(S.base k).1, y⟩ : (S.flow k).point) := by
    rw [hpoints]
    simpa only [mul_zero] using
      E.zero_identity (show (0 : ℝ) ∈ Icc (-T) 0 from
        ⟨by nlinarith [sq_nonneg rho], le_rfl⟩) y (hball_source hy)
  have hscale : B * Q ≤ r⁻¹ ^ 2 := by
    rw [inv_pow, inv_eq_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    calc
      B * Q * r ^ 2 = B * (Q * r ^ 2) := by ring
      _ = B * rho ^ 2 := by rw [hQr]
      _ ≤ 1 := hB
  have hcurvature (s : ℝ) (hs : s ∈ Ioc (-r ^ 2) 0)
      (y : ((S.flow k).slice (S.base k).1).carrier)
      (hy : y ∈ ((S.flow k).metric (S.base k).1).ball x r) :
      |(S.flow k).curvatureNorm (etest.pointMap s hs y)| ≤ r⁻¹ ^ 2 := by
    rw [hpoints]
    exact (E.curvature_bound (Q * s) _ y (hball_source hy)).trans hscale
  exact hnon r hr hcutoff hinterval etest hzero hcurvature

theorem terminal_volume_at_point_of_noncollapsedCylinder
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ}
    {A T B eta kappa r₀ rho : ℝ}
    (N : NoncollapsedControlledBlowupCylinder S k A T B eta kappa r₀)
    {x : ((S.flow k).slice (S.base k).1).carrier}
    (hx : x ∈ S.baseBall k A)
    (hrho : 0 < rho) (hT : rho ^ 2 ≤ T) (hB : B * rho ^ 2 ≤ 1)
    (hcutoff : rho / Real.sqrt (S.scale k) ≤ r₀)
    (hball_source : ((S.flow k).metric (S.base k).1).ball x
      (rho / Real.sqrt (S.scale k)) ⊆ S.baseBall k A) :
    ENNReal.ofReal (kappa * (rho / Real.sqrt (S.scale k)) ^ 3) ≤
      calibratedMetricVolume ((S.flow k).metric (S.base k).1)
        (((S.flow k).metric (S.base k).1).ball x
          (rho / Real.sqrt (S.scale k))) := by
  have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨by nlinarith [sq_nonneg rho], le_rfl⟩
  have hnon : GeneralizedKappaNoncollapsedAt (S.flow k)
      (⟨(S.base k).1, x⟩ : (S.flow k).point) kappa r₀ := by
    simpa only [N.zero_identity hzero x hx] using N.noncollapsed 0 hzero x hx
  exact physical_center_volume_bound N.toControlledBlowupCylinder hnon
    hrho hT hB hcutoff hball_source

theorem scaled_terminal_volume_at_point_of_noncollapsedCylinder
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ}
    {A T B eta kappa r₀ rho : ℝ}
    (N : NoncollapsedControlledBlowupCylinder S k A T B eta kappa r₀)
    {x : ((S.flow k).slice (S.base k).1).carrier}
    (hx : x ∈ S.baseBall k A)
    (hrho : 0 < rho) (hT : rho ^ 2 ≤ T) (hB : B * rho ^ 2 ≤ 1)
    (hcutoff : rho / Real.sqrt (S.scale k) ≤ r₀)
    (hball_source : ((S.flow k).metric (S.base k).1).ball x
      (rho / Real.sqrt (S.scale k)) ⊆ S.baseBall k A) :
    ENNReal.ofReal (kappa * rho ^ 3) ≤
      calibratedMetricVolume
        (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
          (S.scale k) (S.base_scalar_pos k))
        (RiemannianMetric.ball
          (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
            (S.scale k) (S.base_scalar_pos k)) x rho) := by
  have hQ : 0 < S.scale k := S.base_scalar_pos k
  have hsqrt : 0 < Real.sqrt (S.scale k) := Real.sqrt_pos.mpr hQ
  let g : RiemannianMetric 3 ((S.flow k).slice (S.base k).1).carrier :=
    (S.flow k).metric (S.base k).1
  let h : RiemannianMetric 3 ((S.flow k).slice (S.base k).1).carrier :=
    M13.scaleSmoothMetric g (S.scale k) (S.base_scalar_pos k)
  have himage := M13.homothety_ball_image g h
    (Diffeomorph.refl (𝓡 3) ((S.flow k).slice (S.base k).1).carrier ∞)
    (S.scale k) (S.base_scalar_pos k)
    (M13.identity_metricHomothety g (S.scale k) (S.base_scalar_pos k)) x
    (rho / Real.sqrt (S.scale k))
  have hvolume := M13.homothety_volume_image g h
    (Diffeomorph.refl (𝓡 3) ((S.flow k).slice (S.base k).1).carrier ∞)
    (S.scale k) (S.base_scalar_pos k)
    (M13.identity_metricHomothety g (S.scale k) (S.base_scalar_pos k))
    (g.ball x (rho / Real.sqrt (S.scale k)))
  have hsource := terminal_volume_at_point_of_noncollapsedCylinder N hx
    hrho hT hB hcutoff hball_source
  have hsource' : ENNReal.ofReal (kappa * (rho / Real.sqrt (S.scale k)) ^ 3) ≤
      calibratedMetricVolume g (g.ball x (rho / Real.sqrt (S.scale k))) := by
    simpa only [g] using hsource
  simp only [Diffeomorph.coe_refl, image_id, id_eq] at himage hvolume
  have hball' : g.ball x (rho / Real.sqrt (S.scale k)) = h.ball x rho := by
    simpa only [mul_div_cancel₀ _ hsqrt.ne'] using himage
  rw [hball'] at hvolume
  have hfactor : Real.rpow (S.scale k) ((3 : ℝ) / 2) =
      Real.sqrt (S.scale k) ^ 3 := by
    rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt (3 : ℝ) hQ.le]
    norm_num
  have hvolume' : calibratedMetricVolume h (h.ball x rho) =
      ENNReal.ofReal (Real.sqrt (S.scale k) ^ 3) *
        calibratedMetricVolume g (h.ball x rho) := by
    convert hvolume using 1
    exact congrArg (fun z : ℝ≥0∞ =>
      z * calibratedMetricVolume g (h.ball x rho))
      (congrArg ENNReal.ofReal hfactor).symm
  rw [hvolume']
  have heq : ENNReal.ofReal (kappa * rho ^ 3) =
      ENNReal.ofReal (Real.sqrt (S.scale k) ^ 3) *
        ENNReal.ofReal (kappa * (rho / Real.sqrt (S.scale k)) ^ 3) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hsqrt.le 3)]
    congr 1
    field_simp
  rw [heq]
  rw [hball'] at hsource'
  exact mul_le_mul_right hsource' _

end PoincareConjecture.M30
