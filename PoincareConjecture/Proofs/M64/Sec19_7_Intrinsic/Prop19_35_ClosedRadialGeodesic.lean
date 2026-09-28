import PoincareConjecture.Proofs.M64.Mathlib.SmoothClosedExtension
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalMetric





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_exists_closed_radial_unit_geodesic
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (hzeroOmega : (0 : AnnulusCoordinates) ∈ Omega)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega)
    (hmetric : ∀ v w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w)
    (hgeo : ∀ v ∈ Omega, N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Omega})
    (hstar : ∀ v ∈ Omega, ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega)
    {v : AnnulusCoordinates} (hv : v ∈ Omega) (hne : v ≠ 0) :
    ∃ g : ℝ → AnnulusCoordinates,
      ContDiff ℝ ∞ g ∧ N.metric.IsGeodesicOn g (Icc 0 ‖v‖) ∧
      (∀ t ∈ Icc 0 ‖v‖, N.metric.inner (g t) (deriv g t) (deriv g t) = 1) ∧
      g 0 = e 0 ∧ g ‖v‖ = e v ∧
      (∀ t ∈ Icc 0 ‖v‖, g t = e ((t / ‖v‖) • v)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, g (‖v‖ * t) = e (t • v)) ∧
      deriv g ‖v‖ = fderiv ℝ e v (‖v‖⁻¹ • v) := by
  let ell : ℝ := ‖v‖
  have hell : 0 < ell := norm_pos_iff.mpr hne
  let c : ℝ → AnnulusCoordinates := fun t => (ell⁻¹ * t) • v
  let q : ℝ → AnnulusCoordinates := fun t => e (c t)
  let I : Set ℝ := c ⁻¹' Omega
  have hc : ContDiff ℝ ∞ c := (contDiff_const.mul contDiff_id).smul contDiff_const
  have hI : IsOpen I := hOmega.preimage hc.continuous
  have hscale (t : ℝ) (ht : t ∈ Icc 0 ell) : ell⁻¹ * t ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (inv_nonneg.mpr hell.le) ht.1, ?_⟩
    calc
      ell⁻¹ * t ≤ ell⁻¹ * ell := mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.mpr hell.le)
      _ = 1 := inv_mul_cancel₀ hell.ne'
  have hinterval : Icc 0 ell ⊆ I := fun t ht => hstar v hv _ (hscale t ht)
  have hq : ContDiffOn ℝ ∞ q I :=
    (contMDiffOn_iff_contDiffOn.mp he).comp hc.contDiffOn (fun _ ht => ht)
  have hqgeo : N.metric.IsGeodesicOn q I := (hgeo v hv).comp_mul ell⁻¹
  obtain ⟨g, hg, hgq⟩ := m64_exists_contDiff_eq_nhds_of_isClosed
    isClosed_Icc hI hinterval hq
  have hggeo : N.metric.IsGeodesicOn g (Icc 0 ell) := by
    intro t ht
    obtain ⟨p, u, w, hlocal⟩ := hqgeo t (hinterval ht)
    refine ⟨p, u, w, ?_⟩
    filter_upwards [hlocal, hgq t ht] with s hs hgs
    exact ⟨hgs.trans hs.1, hs.2⟩
  have hzI : (0 : ℝ) ∈ Icc 0 ell := ⟨le_rfl, hell.le⟩
  have hg0 : g 0 = e 0 := by
    simpa only [q, c, mul_zero, zero_smul] using (hgq 0 hzI).self_of_nhds
  have hcd (t : ℝ) : HasDerivAt c (ell⁻¹ • v) t := by
    simpa only [c, mul_one] using!
      (((hasDerivAt_id t).const_mul ell⁻¹).smul_const v)
  have hqd (t : ℝ) (ht : t ∈ Icc 0 ell) :
      deriv q t = fderiv ℝ e (c t) (ell⁻¹ • v) := by
    have hed := (((contMDiffOn_iff_contDiffOn.mp he).contDiffAt
      (hOmega.mem_nhds (hinterval ht))).differentiableAt (by simp)).hasFDerivAt
    exact (hed.comp_hasDerivAt t (hcd t)).deriv
  have hnorm : ‖ell⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hell.le)]
    exact inv_mul_cancel₀ hell.ne'
  have hqd0 : deriv q 0 = fderiv ℝ e 0 (ell⁻¹ • v) := by
    have hed : HasFDerivAt e (fderiv ℝ e 0) (c 0) := by
      simpa only [c, mul_zero, zero_smul] using
        (((contMDiffOn_iff_contDiffOn.mp he).contDiffAt
          (hOmega.mem_nhds hzeroOmega)).differentiableAt (by simp)).hasFDerivAt
    exact (hed.comp_hasDerivAt 0 (hcd 0)).deriv
  have hunit0 : N.metric.inner (g 0) (curveVelocity (n := 2) g 0)
      (curveVelocity (n := 2) g 0) = 1 := by
    rw [m64Intrinsic_curveVelocity_eq_deriv, (hgq 0 hzI).deriv_eq, hqd0, hg0]
    simpa only [mfderiv_eq_fderiv,
      real_inner_self_eq_norm_sq, hnorm, one_pow] using! hmetric (ell⁻¹ • v) (ell⁻¹ • v)
  have hunit (t : ℝ) (ht : t ∈ Icc 0 ell) :
      N.metric.inner (g t) (deriv g t) (deriv g t) = 1 := by
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using
      m64Intrinsic_geodesic_velocity_unit N hell hggeo Subset.rfl hunit0 t ht
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ell * t ∈ Icc 0 ell := by
    refine ⟨mul_nonneg hell.le ht.1, ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 hell.le
  have hvalue (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g (ell * t) = e (t • v) := by
    simpa only [q, c, ← mul_assoc, inv_mul_cancel₀ hell.ne', one_mul] using
      (hgq (ell * t) (htime t ht)).self_of_nhds
  refine ⟨g, hg, hggeo, hunit, hg0, ?_, ?_, hvalue, ?_⟩
  · simpa only [mul_one, one_smul] using hvalue 1 ⟨zero_le_one, le_rfl⟩
  · intro t ht
    simpa only [q, c, div_eq_mul_inv, mul_comm] using (hgq t ht).self_of_nhds
  · rw [(hgq ell ⟨hell.le, le_rfl⟩).deriv_eq, hqd ell ⟨hell.le, le_rfl⟩]
    simp only [c, inv_mul_cancel₀ hell.ne', one_smul, ell]

end PoincareConjecture
