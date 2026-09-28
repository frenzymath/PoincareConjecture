import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalVariation
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_normal_variation_initial_fderiv_injective
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0)
    {F : ℝ × ℝ → AnnulusCoordinates} {a : ℝ} {normal : AnnulusCoordinates}
    (hF : DifferentiableAt ℝ F (a, 0))
    (hboundary : (fun x => F (x, 0)) =ᶠ[𝓝 a] intrinsicAnnulusBoundary radius)
    (hnormal : HasDerivAt (fun t => F (a, t)) normal 0)
    (hunit : N.metric.inner (intrinsicAnnulusBoundary radius a) normal normal = 1)
    (horth : N.metric.inner (intrinsicAnnulusBoundary radius a) normal
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a) = 0) :
    Function.Injective (fderiv ℝ F (a, 0)) := by
  let velocity : AnnulusCoordinates := curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a
  let L := fderiv ℝ F (a, 0)
  have hfst : L (1, 0) = velocity := by
    have hd := hF.hasFDerivAt.comp_hasDerivAt (l := F) (f := fun x => (x, (0 : ℝ))) a
      ((hasDerivAt_id a).prodMk (hasDerivAt_const a (0 : ℝ)))
    have hg : HasDerivAt (fun x => F (x, 0)) velocity a := by
      have h := m64Intrinsic_hasDerivAt_boundary radius a
      rw [← m64Intrinsic_boundary_velocity] at h
      exact h.congr_of_eventuallyEq hboundary
    exact hd.unique hg
  have hsnd : L (0, 1) = normal := by
    have hd := hF.hasFDerivAt.comp_hasDerivAt (l := F) (f := fun t => (a, t)) 0
      ((hasDerivAt_const 0 a).prodMk (hasDerivAt_id 0))
    exact hd.unique hnormal
  have hL (z : ℝ × ℝ) : L z = z.1 • velocity + z.2 • normal := by
    have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
    calc
      L z = L (z.1 • (1, 0) + z.2 • (0, 1)) := congrArg L hz
      _ = _ := by rw [map_add, map_smul, map_smul, hfst, hsnd]
  have hvpos : 0 < N.metric.inner (intrinsicAnnulusBoundary radius a) velocity velocity :=
    Real.sqrt_pos.mp (m64Intrinsic_boundarySpeed_pos N hradius a)
  change N.metric.inner (intrinsicAnnulusBoundary radius a) normal velocity = 0 at horth
  have horth' : N.metric.inner (intrinsicAnnulusBoundary radius a) velocity normal = 0 := by
    rw [N.metric.symm]
    exact horth
  apply (injective_iff_map_eq_zero L).mpr
  intro z hz
  have hsecond := congrArg (fun v => N.metric.inner
    (intrinsicAnnulusBoundary radius a) v normal) hz
  rw [hL] at hsecond
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
    horth', hunit, mul_zero, zero_add, mul_one, map_zero, zero_apply] at hsecond
  have hfirst := congrArg (fun v => N.metric.inner
    (intrinsicAnnulusBoundary radius a) v velocity) hz
  rw [hL] at hfirst
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
    horth, mul_zero, add_zero, map_zero, zero_apply] at hfirst
  have hzero : z.1 = 0 := (mul_eq_zero.mp hfirst).resolve_right hvpos.ne'
  exact Prod.ext hzero hsecond

theorem m64Intrinsic_normal_variation_regular_neighborhood
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0)
    {F : ℝ × ℝ → AnnulusCoordinates} {a : ℝ} {normal : AnnulusCoordinates}
    (hF : ContDiffAt ℝ ∞ F (a, 0))
    (hboundary : (fun x => F (x, 0)) =ᶠ[𝓝 a] intrinsicAnnulusBoundary radius)
    (hnormal : HasDerivAt (fun t => F (a, t)) normal 0)
    (hunit : N.metric.inner (intrinsicAnnulusBoundary radius a) normal normal = 1)
    (horth : N.metric.inner (intrinsicAnnulusBoundary radius a) normal
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a) = 0) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (a, 0) ∈ U ∧
      ∀ z ∈ U, Function.Injective (fderiv ℝ F z) := by
  have hinj := m64Intrinsic_normal_variation_initial_fderiv_injective N hradius
    (hF.differentiableAt (by simp)) hboundary hnormal hunit horth
  have hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ AnnulusCoordinates := by simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let A : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates :=
    (LinearEquiv.ofBijective (fderiv ℝ F (a, 0)).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = fderiv ℝ F (a, 0) := rfl
  have hnear : {z : ℝ × ℝ | (fderiv ℝ F z).IsInvertible} ∈ 𝓝 (a, 0) := by
    have h := A.nhds
    rw [hA] at h
    exact ((hF.fderiv_right (m := 0) (by simp)).continuousAt).preimage_mem_nhds h
  obtain ⟨U, hUsub, hU, ha⟩ := mem_nhds_iff.mp hnear
  exact ⟨U, hU, ha, fun z hz => (hUsub hz).injective⟩

theorem m64Intrinsic_inward_curve_enters_annulus
    {gamma : ℝ → AnnulusCoordinates} {a : ℝ} {v : AnnulusCoordinates}
    (hzero : gamma 0 = intrinsicAnnulusBoundary 1 a)
    (hderiv : HasDerivAt gamma v 0)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a) v) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ioo (0 : ℝ) epsilon, 1 < ‖gamma t‖ ∧ ‖gamma t‖ < 2 := by
  have hnorm : ‖gamma 0‖ = 1 := by
    have h := m64Intrinsic_boundary_self_inner 1 a
    rw [real_inner_self_eq_norm_sq] at h
    rw [hzero]
    nlinarith [norm_nonneg (intrinsicAnnulusBoundary 1 a)]
  have hnormsq : HasDerivAt (fun t => ‖gamma t‖ ^ 2)
      (2 * inner ℝ (gamma 0) v) 0 := by
    convert! (hasStrictFDerivAt_norm_sq (gamma 0)).hasFDerivAt.comp_hasDerivAt
      (l := fun p : AnnulusCoordinates => ‖p‖ ^ 2) (f := gamma) 0 hderiv using 1
    simp only [two_smul, add_apply, innerSL_apply_apply, two_mul]
  have hpos : 0 < 2 * inner ℝ (gamma 0) v := by rw [hzero]; positivity
  have hslope := hnormsq.tendsto_slope_zero_right
  have heventual : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < ‖gamma t‖ := by
    filter_upwards [hslope.eventually (Ioi_mem_nhds hpos), self_mem_nhdsWithin] with t ht htp
    change 0 < t at htp
    simp only [zero_add, hnorm, one_pow, smul_eq_mul] at ht
    have hsq : 0 < ‖gamma t‖ ^ 2 - 1 := by
      have h := (mul_pos_iff_of_pos_left (inv_pos.mpr htp)).mp ht
      exact h
    nlinarith [norm_nonneg (gamma t)]
  have hupper : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖gamma t‖ < 2 := by
    exact (hderiv.continuousAt.norm.eventually (Iio_mem_nhds (by
      change ‖gamma 0‖ < 2
      rw [hnorm]
      norm_num))).filter_mono nhdsWithin_le_nhds
  obtain ⟨epsilon, hepsilon, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp (heventual.and hupper)
  exact ⟨epsilon, hepsilon, fun t ht => hsub ⟨ht.1, ht.2.le⟩⟩

end PoincareConjecture
