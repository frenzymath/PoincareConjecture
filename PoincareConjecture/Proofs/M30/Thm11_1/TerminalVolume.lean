import PoincareConjecture.Proofs.M30.Thm11_1.ControlledCylinders
import PoincareConjecture.Proofs.M30.Generalized.PhysicalClock
import PoincareConjecture.Proofs.M30.Generalized.TerminalMetric
import PoincareConjecture.Proofs.M13.Volume

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem terminal_volume_of_controlledCylinder
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T B eta kappa r₀ rho : ℝ}
    (E : ControlledBlowupCylinder S k A T B eta)
    (hnon : GeneralizedKappaNoncollapsedAt (S.flow k) (S.base k) kappa r₀)
    (hrho : 0 < rho) (hA : rho ≤ A) (hT : rho ^ 2 ≤ T)
    (hB : B * rho ^ 2 ≤ 1) (hcutoff : rho / Real.sqrt (S.scale k) ≤ r₀) :
    ENNReal.ofReal (kappa * (rho / Real.sqrt (S.scale k)) ^ 3) ≤
      calibratedMetricVolume ((S.flow k).metric (S.base k).1) (S.baseBall k rho) := by
  let Q := S.scale k
  let r := rho / Real.sqrt Q
  have hQ : 0 < Q := S.base_scalar_pos k
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hr : 0 < r := div_pos hrho hsqrt
  have hQr : Q * r ^ 2 = rho ^ 2 := by
    dsimp only [r]
    rw [div_pow, Real.sq_sqrt hQ.le, mul_div_cancel₀ _ hQ.ne']
  have hclock : Icc (-r ^ 2) 0 ⊆ (fun s : ℝ => Q * s) ⁻¹' Icc (-T) 0 := by
    intro s hs
    constructor
    · have h := mul_le_mul_of_nonneg_left hs.1 hQ.le
      nlinarith [hQr]
    · exact mul_nonpos_of_nonneg_of_nonpos hQ.le hs.2
  have hspace : S.baseBall k rho ⊆ S.baseBall k A := by
    intro x hx
    change ((S.flow k).metric (S.base k).1).edist (S.base k).2 x <
      ENNReal.ofReal (rho / Real.sqrt Q) at hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hA hsqrt.le))
  let ep := Cylinder.physicalTime E.embedding hclock
  let etest : GeneralizedFlowCylinder (S.flow k) ((S.flow k).slice (S.base k).1)
      (S.base k).1 1 (Ioc (-r ^ 2) 0) (S.baseBall k rho) :=
    Cylinder.restrict ep Ioc_subset_Icc_self hspace
  have hpoints (s : ℝ) (hs : s ∈ Ioc (-r ^ 2) 0)
      (x : ((S.flow k).slice (S.base k).1).carrier) :
      etest.pointMap s hs x =
        E.embedding.pointMap (Q * s) (hclock (Ioc_subset_Icc_self hs)) x :=
    Cylinder.physicalTime_pointMap E.embedding hclock s (Ioc_subset_Icc_self hs) x
  have hinterval : Ioc ((S.base k).1 - r ^ 2) (S.base k).1 ⊆ (S.flow k).interval := by
    intro t ht
    have hs : t - (S.base k).1 ∈ Icc (-r ^ 2) 0 := by
      constructor <;> linarith [ht.1, ht.2]
    have h := ((S.flow k).slice_nonempty_iff _).mp
      ⟨ep.forward (t - (S.base k).1) hs (S.base k).2⟩
    have heq : (S.base k).1 + (t - (S.base k).1) / 1 = t := by ring
    rwa [heq] at h
  have hzero (h₀ : (0 : ℝ) ∈ Ioc (-r ^ 2) 0)
      (x : ((S.flow k).slice (S.base k).1).carrier) (hx : x ∈ S.baseBall k rho) :
      etest.pointMap 0 h₀ x = (⟨(S.base k).1, x⟩ : (S.flow k).point) := by
    rw [hpoints]
    simpa only [mul_zero] using
      E.zero_identity (show (0 : ℝ) ∈ Icc (-T) 0 from
        ⟨by nlinarith [sq_nonneg rho], le_rfl⟩) x (hspace hx)
  have hscale : B * Q ≤ r⁻¹ ^ 2 := by
    rw [inv_pow, inv_eq_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    calc
      B * Q * r ^ 2 = B * (Q * r ^ 2) := by ring
      _ = B * rho ^ 2 := by rw [hQr]
      _ ≤ 1 := hB
  have hcurvature (s : ℝ) (hs : s ∈ Ioc (-r ^ 2) 0)
      (x : ((S.flow k).slice (S.base k).1).carrier) (hx : x ∈ S.baseBall k rho) :
      |(S.flow k).curvatureNorm (etest.pointMap s hs x)| ≤ r⁻¹ ^ 2 := by
    rw [hpoints]
    exact (E.curvature_bound (Q * s) _ x (hspace hx)).trans hscale
  exact hnon r hr hcutoff hinterval etest hzero hcurvature

theorem exists_eventually_terminal_volume_lower_bound
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) :
    ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1) (S.baseBall k rho) := by
  obtain ⟨T, hT, B, _hB, hcyl⟩ :=
    exists_radius_dependent_controlled_cylinders hC H hbound 1 zero_lt_one
  let K := max B 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  let d := min 1 (min (Real.sqrt T) (Real.sqrt K)⁻¹)
  let rho := d / 2
  let v := kappa * rho ^ 3
  have hd : 0 < d := lt_min zero_lt_one
    (lt_min (Real.sqrt_pos.mpr hT) (inv_pos.mpr (Real.sqrt_pos.mpr hK)))
  have hrho : 0 < rho := half_pos hd
  have hrhod : rho ≤ d := by dsimp only [rho]; linarith
  have hrho1 : rho ≤ 1 := hrhod.trans (min_le_left _ _)
  have hrhoT : rho ≤ Real.sqrt T :=
    hrhod.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrhoK : rho ≤ (Real.sqrt K)⁻¹ :=
    hrhod.trans ((min_le_right _ _).trans (min_le_right _ _))
  have htime : rho ^ 2 ≤ T := by
    calc
      rho ^ 2 ≤ (Real.sqrt T) ^ 2 := pow_le_pow_left₀ hrho.le hrhoT 2
      _ = T := Real.sq_sqrt hT.le
  have hcurv : B * rho ^ 2 ≤ 1 := by
    calc
      B * rho ^ 2 ≤ K * rho ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left B 1) (sq_nonneg rho)
      _ ≤ K * ((Real.sqrt K)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrho.le hrhoK 2) hK.le
      _ = 1 := by rw [inv_pow, Real.sq_sqrt hK.le, mul_inv_cancel₀ hK.ne']
  refine ⟨rho, v, hrho, mul_pos H.kappa_pos (pow_pos hrho 3), ?_⟩
  filter_upwards [hcyl 1 zero_lt_one, H.noncollapsed_at_zero 1 zero_lt_one,
    S.scalar_diverges.eventually_ge_atTop ((rho / r₀) ^ 2)] with k hE hnon hlarge
  obtain ⟨E⟩ := hE
  have hsqrt : 0 < Real.sqrt (S.scale k) := Real.sqrt_pos.mpr (S.base_scalar_pos k)
  have hcutoff : rho / Real.sqrt (S.scale k) ≤ r₀ := by
    apply (div_le_iff₀ hsqrt).mpr
    have h := (div_le_iff₀ H.radius_pos).mp (Real.le_sqrt_of_sq_le hlarge)
    simpa only [GeneralizedBlowupSequence.scale, mul_comm] using h
  have hbase : (S.base k).2 ∈ S.baseBall k 1 := by
    change ((S.flow k).metric (S.base k).1).edist (S.base k).2 (S.base k).2 <
      ENNReal.ofReal (1 / Real.sqrt (S.scale k))
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos zero_lt_one hsqrt)
  have hv := terminal_volume_of_controlledCylinder E (hnon (S.base k).2 hbase)
    hrho hrho1 htime hcurv hcutoff
  simpa only [v, div_pow, mul_div_assoc] using hv

theorem scaled_terminal_volume_lower_bound
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {rho v : ℝ}
    (hv : ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
      calibratedMetricVolume ((S.flow k).metric (S.base k).1) (S.baseBall k rho)) :
    ENNReal.ofReal v ≤ calibratedMetricVolume
      (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
        (S.scale k) (S.base_scalar_pos k))
      (RiemannianMetric.ball
        (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
          (S.scale k) (S.base_scalar_pos k)) (S.base k).2 rho) := by
  rw [scaled_terminal_ball_eq_baseBall]
  have hQ : 0 < S.scale k := S.base_scalar_pos k
  have hsqrt : 0 < Real.sqrt (S.scale k) := Real.sqrt_pos.mpr hQ
  have hfactor : Real.rpow (S.scale k) ((3 : ℝ) / 2) =
      Real.sqrt (S.scale k) ^ 3 := by
    rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt (3 : ℝ) hQ.le]
    norm_num
  have hvolume := M13.homothety_volume_image ((S.flow k).metric (S.base k).1)
    (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k))
    (Diffeomorph.refl (𝓡 3) ((S.flow k).slice (S.base k).1).carrier ∞)
    (S.scale k) (S.base_scalar_pos k)
    (M13.identity_metricHomothety ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k)) (S.baseBall k rho)
  simp only [Diffeomorph.coe_refl, image_id, Nat.cast_ofNat] at hvolume
  rw [hfactor] at hvolume
  rw [hvolume]
  have heq : ENNReal.ofReal v = ENNReal.ofReal (Real.sqrt (S.scale k) ^ 3) *
      ENNReal.ofReal (v / Real.sqrt (S.scale k) ^ 3) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hsqrt.le 3),
      mul_div_cancel₀ _ (pow_ne_zero 3 hsqrt.ne')]
  rw [heq]
  exact mul_le_mul_right hv _

theorem exists_eventually_scaled_terminal_volume_lower_bound
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) :
    ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal v ≤ calibratedMetricVolume
        (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
          (S.scale k) (S.base_scalar_pos k))
        (RiemannianMetric.ball
          (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
            (S.scale k) (S.base_scalar_pos k)) (S.base k).2 rho) := by
  obtain ⟨rho, v, hrho, hv, hvolume⟩ :=
    exists_eventually_terminal_volume_lower_bound hC H hbound
  refine ⟨rho, v, hrho, hv, ?_⟩
  filter_upwards [hvolume] with k hk
  exact scaled_terminal_volume_lower_bound hk

end PoincareConjecture.M30
