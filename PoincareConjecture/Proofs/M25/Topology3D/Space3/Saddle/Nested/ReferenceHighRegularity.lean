import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighCritical
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SouthernSphereChart
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem reference_high_sphere_regularity
    (ws wm d : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32)) :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
    let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
    let qs : UnitTwoSphere := -southSpherePoint (-vs)
    let qm : UnitTwoSphere := -southSpherePoint (-vm)
    let k : ℝ := U vs
    let mu : ℝ := U vm
    let H : UnitTwoSphere → ℝ := fun q =>
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H ∧
    (37 : ℝ) / 32 < k ∧ k < 5 / 4 ∧ 5 / 4 < mu ∧
    heightCoordinates (qs : E3) = (vs, ws) ∧
    heightCoordinates (qm : E3) = (vm, wm) ∧
    H qs = k + d ∧ H qm = mu + d ∧
    (∀ q : UnitTwoSphere, (17 : ℝ) / 16 < H q - d →
      0 < (heightCoordinates (q : E3)).2 ∧
      ‖(heightCoordinates (q : E3)).1‖ < 1 ∧
      H q = U (heightCoordinates (q : E3)).1 + d ∧
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H q = 0 ↔ q = qs ∨ q = qm)) ∧
    (∀ q : UnitTwoSphere, (17 : ℝ) / 16 < H q - d →
      H q ≠ k + d → H q ≠ mu + d →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H q ≠ 0) ∧
    ∀ a b : ℝ,
      (((17 : ℝ) / 16 < a ∧ b < k) ∨ (k < a ∧ b < mu)) →
      ∀ q : UnitTwoSphere, H q ∈ Set.Icc (a + d) (b + d) →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H q ≠ 0 := by
  classical
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let g : ℝ → ℝ := fun w => (2 - 1 / w) * Real.sqrt (1 - w ^ 2)
  let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
  let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
  let up : E2 → UnitTwoSphere := fun v => -southSpherePoint (-v)
  let qs : UnitTwoSphere := up vs
  let qm : UnitTwoSphere := up vm
  let k : ℝ := U vs
  let mu : ℝ := U vm
  let H : UnitTwoSphere → ℝ := fun q =>
    (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2
  let pi : UnitTwoSphere → E2 := fun q => (heightCoordinates (q : E3)).1
  change ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H ∧ _
  obtain ⟨ws0, wm0, hwslo0, hwshi0, hwsroot0, hwmlo0, hwmhi0, hwmroot0,
    hvs, hvm, hklo, hkhi, hmulo, hU, hvmcrit, _hmax, _hunique, hclass,
    _hpositive, _hinjective⟩ := exists_reference_high_critical_geometry
  obtain ⟨w, _hw, hwunique⟩ := exists_unique_nestedReference_saddle_root
  have hseq : ws0 = ws := (hwunique ws0 ⟨hwslo0, hwshi0, hwsroot0⟩).trans
    (hwunique ws ⟨hwslo, hwshi, hwsroot⟩).symm
  subst ws0
  have hgder (w : ℝ) (hw : w ∈ Ioo (0 : ℝ) (1 / 2)) :
      HasDerivAt g ((1 - 2 * w ^ 3) / (w ^ 2 * Real.sqrt (1 - w ^ 2))) w ∧
        0 < (1 - 2 * w ^ 3) / (w ^ 2 * Real.sqrt (1 - w ^ 2)) := by
    have hrad0 : 0 < 1 - w ^ 2 := by nlinarith only [hw.1, hw.2]
    have hcube := pow_le_pow_left₀ hw.1.le hw.2.le 3
    norm_num at hcube
    let r : ℝ := Real.sqrt (1 - w ^ 2)
    have hr0 : 0 < r := Real.sqrt_pos.mpr hrad0
    have hr2 : r ^ 2 = 1 - w ^ 2 := Real.sq_sqrt hrad0.le
    have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / w ^ 2) w :=
      (hasDerivAt_id w).inv hw.1.ne'
    have ha : HasDerivAt (fun x : ℝ => 2 - 1 / x) (1 / w ^ 2) w := by
      simpa only [one_div, neg_div, neg_neg] using hinv.const_sub (2 : ℝ)
    have hradder : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * w) w := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one, neg_mul] using ((hasDerivAt_id w).pow 2).const_sub (1 : ℝ)
    have hh : HasDerivAt g
        ((1 / w ^ 2) * r + (2 - 1 / w) * ((-2 * w) / (2 * r))) w :=
      ha.mul (hradder.sqrt hrad0.ne')
    have halg : (1 / w ^ 2) * r + (2 - 1 / w) * ((-2 * w) / (2 * r)) =
        (1 - 2 * w ^ 3) / (w ^ 2 * r) := by
      calc
        _ = r ^ 2 / (w ^ 2 * r) + (w ^ 2 - 2 * w ^ 3) / (w ^ 2 * r) := by
          congr 1
          · field_simp [hw.1.ne', hr0.ne']
          · field_simp [hw.1.ne', hr0.ne']
            ring
        _ = (1 - 2 * w ^ 3) / (w ^ 2 * r) := by
          rw [← add_div]
          congr 1
          nlinarith only [hr2]
    rw [halg] at hh
    exact ⟨hh, div_pos (by linarith only [hcube]) (mul_pos (sq_pos_of_pos hw.1) hr0)⟩
  have hgmono : StrictMonoOn g (Ioo (0 : ℝ) (1 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun w hw => (hgder w hw).1.continuousAt.continuousWithinAt)
    intro w hw
    obtain ⟨hd, hp⟩ := hgder w (interior_subset hw)
    rw [hd.deriv]
    exact hp
  have hmeq : wm0 = wm := hgmono.injOn ⟨hwmlo0, hwmhi0⟩ ⟨hwmlo, hwmhi⟩
    (hwmroot0.trans hwmroot.symm)
  subst wm0
  change ‖vs‖ < 1 at hvs
  change ‖vm‖ < 1 at hvm
  change (37 : ℝ) / 32 < k at hklo
  change k < 5 / 4 at hkhi
  change (5 : ℝ) / 4 < mu at hmulo
  change ContDiffOn ℝ ∞ U (ball (0 : E2) 1) at hU
  change fderiv ℝ U vm = 0 at hvmcrit
  change ∀ v ∈ ball (0 : E2) 1, (17 : ℝ) / 16 < U v →
    fderiv ℝ U v = 0 → v = vs ∨ v = vm at hclass
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hH : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H :=
    contDiff_snd.contMDiff.comp (heightCoordinates.contDiff.contMDiff.comp
      ((nestedReferenceDiffeomorph d).contMDiff_toFun.comp contMDiff_coe_sphere))
  have hpi : ContMDiff (𝓡 2) 𝓘(ℝ, E2) ∞ pi :=
    contDiff_fst.contMDiff.comp
      (heightCoordinates.contDiff.contMDiff.comp contMDiff_coe_sphere)
  have hNorm (v : E2) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hformula (q : UnitTwoSphere) : H q =
      ‖pi q‖ ^ 2 + (heightCoordinates (q : E3)).2 + pi q 0 / 32 + d := by
    dsimp only [H]
    rw [(nestedReferenceDiffeomorph_apply_symm d).1 (q : E3),
      heightCoordinates_snd_apply, hNorm]
    change (q : E3) 2 + (q : E3) 0 ^ 2 + (q : E3) 1 ^ 2 + (q : E3) 0 / 32 + d =
      ((q : E3) 0 ^ 2 + (q : E3) 1 ^ 2) + (q : E3) 2 + (q : E3) 0 / 32 + d
    ring
  have hupCoordinates (v : E2) (hv : ‖v‖ < 1) :
      heightCoordinates (up v : E3) = (v, Real.sqrt (1 - ‖v‖ ^ 2)) := by
    change heightCoordinates ((-southSpherePoint (-v) : UnitTwoSphere) : E3) = _
    rw [coe_neg_sphere, map_neg,
      southSpherePoint_coordinates (-v) (by simpa only [norm_neg] using hv), norm_neg]
    change (-(-v), -(-Real.sqrt (1 - ‖v‖ ^ 2))) =
      (v, Real.sqrt (1 - ‖v‖ ^ 2))
    simp only [neg_neg]
  have hupSmooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ up (ball (0 : E2) 1) := by
    have hneg : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E2) ∞
        (fun x : E2 => -x) (ball (0 : E2) 1) :=
      contDiff_id.neg.contMDiff.contMDiffOn
    exact contMDiff_neg_sphere.comp_contMDiffOn
      (southSpherePoint_contMDiffOn.comp hneg (fun x hx => by
        change -x ∈ ball (0 : E2) 1
        simpa only [mem_ball_zero_iff, norm_neg] using hx))
  have hupHeight (v : E2) (hv : ‖v‖ < 1) : H (up v) = U v + d := by
    rw [hformula]
    dsimp only [pi]
    rw [hupCoordinates v hv]
  have hupper (q : UnitTwoSphere) (hq : 0 < (heightCoordinates (q : E3)).2) :
      ‖pi q‖ < 1 ∧ up (pi q) = q ∧ H q = U (pi q) + d := by
    have hs := sphere_height_coordinates_sq q
    change ‖pi q‖ ^ 2 + (heightCoordinates (q : E3)).2 ^ 2 = 1 at hs
    have hv : ‖pi q‖ < 1 := by
      nlinarith only [hs, norm_nonneg (pi q), pow_pos hq 2]
    have hz : Real.sqrt (1 - ‖pi q‖ ^ 2) = (heightCoordinates (q : E3)).2 := by
      rw [show 1 - ‖pi q‖ ^ 2 = (heightCoordinates (q : E3)).2 ^ 2 by
        linarith only [hs], Real.sqrt_sq_eq_abs, abs_of_pos hq]
    have he : up (pi q) = q := by
      apply Subtype.ext
      apply heightCoordinates.injective
      rw [hupCoordinates _ hv, hz]
    have hh := hupHeight (pi q) hv
    rw [he] at hh
    exact ⟨hv, he, hh⟩
  have hhigh (q : UnitTwoSphere) (hq : (17 : ℝ) / 16 < H q - d) :
      0 < (heightCoordinates (q : E3)).2 := by
    have hs := sphere_height_coordinates_sq q
    change ‖pi q‖ ^ 2 + (heightCoordinates (q : E3)).2 ^ 2 = 1 at hs
    have hr : ‖pi q‖ ≤ 1 := by
      nlinarith only [hs, norm_nonneg (pi q), sq_nonneg (heightCoordinates (q : E3)).2]
    have hr2 : ‖pi q‖ ^ 2 ≤ 1 := by
      nlinarith only [hs, sq_nonneg (heightCoordinates (q : E3)).2]
    have hc : pi q 0 ≤ ‖pi q‖ :=
      (le_abs_self _).trans (PiLp.norm_apply_le (pi q) 0)
    rw [hformula] at hq
    by_contra hn
    have hz : (heightCoordinates (q : E3)).2 ≤ 0 := le_of_not_gt hn
    linarith only [hq, hz, hr, hr2, hc]
  have hUdiff (v : E2) (hv : ‖v‖ < 1) : DifferentiableAt ℝ U v :=
    (hU.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv))).differentiableAt
      (by simp)

  have hcritiff (q : UnitTwoSphere) (hq : 0 < (heightCoordinates (q : E3)).2) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H q = 0 ↔ fderiv ℝ U (pi q) = 0 := by
    obtain ⟨hv, hupq, _hh⟩ := hupper q hq
    have hlocal : (H ∘ up) =ᶠ[𝓝 (pi q)] (fun v : E2 => U v + d) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv)] with v hvmem
      exact hupHeight v (mem_ball_zero_iff.mp hvmem)
    have hlocalNative : H =ᶠ[𝓝 q] ((fun v : E2 => U v + d) ∘ pi) := by
      have hzcont : Continuous (fun q : UnitTwoSphere =>
          (heightCoordinates (q : E3)).2) :=
        continuous_snd.comp (heightCoordinates.continuous.comp continuous_subtype_val)
      have hopen : IsOpen {q : UnitTwoSphere | 0 < (heightCoordinates (q : E3)).2} :=
        isOpen_lt continuous_const hzcont
      filter_upwards [hopen.mem_nhds hq] with p hp
      exact (hupper p hp).2.2
    have hup : MDifferentiableAt 𝓘(ℝ, E2) (𝓡 2) up (pi q) :=
      (hupSmooth.contMDiffAt
        (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv))).mdifferentiableAt (by simp)
    constructor
    · intro hzero
      have hc := mfderiv_comp (pi q) (hH.mdifferentiable (by simp) (up (pi q))) hup
      change (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) (H ∘ up) (pi q) : E2 →L[ℝ] ℝ) =
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H (up (pi q)) : E2 →L[ℝ] ℝ).comp
          (mfderiv 𝓘(ℝ, E2) (𝓡 2) up (pi q) : E2 →L[ℝ] E2) at hc
      have hz : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H (up (pi q)) = 0 := hupq.symm ▸ hzero
      rw [hz, ContinuousLinearMap.zero_comp] at hc
      rw [hlocal.mfderiv_eq, mfderiv_eq_fderiv, fderiv_add_const] at hc
      exact hc
    · intro hzero
      have hc := mfderiv_comp q ((hUdiff (pi q) hv).add_const d).mdifferentiableAt
        (hpi.mdifferentiable (by simp) q)
      change (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) ((fun v : E2 => U v + d) ∘ pi) q :
          E2 →L[ℝ] ℝ) =
        (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) (fun v : E2 => U v + d) (pi q) : E2 →L[ℝ] ℝ).comp
          (mfderiv (𝓡 2) 𝓘(ℝ, E2) pi q : E2 →L[ℝ] E2) at hc
      have hz : mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) (fun v : E2 => U v + d) (pi q) = 0 := by
        rw [mfderiv_eq_fderiv, fderiv_add_const]
        exact hzero
      rw [hz, ContinuousLinearMap.zero_comp] at hc
      exact hlocalNative.mfderiv_eq.trans hc
  have hwspos : 0 < ws := by linarith only [hwslo]
  have hwssq : 0 < 1 - ws ^ 2 := by nlinarith only [hwslo, hwshi]
  have hwmsq : 0 < 1 - wm ^ 2 := by nlinarith only [hwmlo, hwmhi]
  have hvssq : ‖vs‖ ^ 2 = 1 - ws ^ 2 := by
    rw [hNorm]
    change (-Real.sqrt (1 - ws ^ 2)) ^ 2 + (0 : ℝ) ^ 2 = _
    rw [neg_sq, Real.sq_sqrt hwssq.le]
    ring
  have hvmsq : ‖vm‖ ^ 2 = 1 - wm ^ 2 := by
    rw [hNorm]
    change (Real.sqrt (1 - wm ^ 2)) ^ 2 + (0 : ℝ) ^ 2 = _
    rw [Real.sq_sqrt hwmsq.le]
    ring
  have hvsroot : Real.sqrt (1 - ‖vs‖ ^ 2) = ws := by
    rw [hvssq, sub_sub_cancel, Real.sqrt_sq_eq_abs, abs_of_pos hwspos]
  have hvmroot : Real.sqrt (1 - ‖vm‖ ^ 2) = wm := by
    rw [hvmsq, sub_sub_cancel, Real.sqrt_sq_eq_abs, abs_of_pos hwmlo]
  have hqscoord : heightCoordinates (qs : E3) = (vs, ws) := by
    change heightCoordinates (up vs : E3) = _
    rw [hupCoordinates vs hvs, hvsroot]
  have hqmcoord : heightCoordinates (qm : E3) = (vm, wm) := by
    change heightCoordinates (up vm : E3) = _
    rw [hupCoordinates vm hvm, hvmroot]
  have hqspos : 0 < (heightCoordinates (qs : E3)).2 := by
    rw [hqscoord]
    exact hwspos
  have hqmpos : 0 < (heightCoordinates (qm : E3)).2 := by
    rw [hqmcoord]
    exact hwmlo
  have hHqs : H qs = k + d := hupHeight vs hvs
  have hHqm : H qm = mu + d := hupHeight vm hvm
  have hvscrit : fderiv ℝ U vs = 0 := by
    let P : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
    let A : ℝ := 2 - 1 / Real.sqrt (1 - ‖vs‖ ^ 2)
    have hrad : 0 < 1 - ‖vs‖ ^ 2 := by
      nlinarith only [hvs, norm_nonneg vs]
    have hspos : 0 < Real.sqrt (1 - ‖vs‖ ^ 2) := Real.sqrt_pos.mpr hrad
    have hfirst : HasFDerivAt U (A • innerSL ℝ vs + (1 / 32 : ℝ) • P) vs := by
      have hsq := (hasStrictFDerivAt_norm_sq vs).hasFDerivAt
      have hs := (hsq.const_sub (1 : ℝ)).sqrt hrad.ne'
      have hp := (P.hasFDerivAt (x := vs)).const_smul (1 / 32 : ℝ)
      have hh := (hsq.add hs).add hp
      convert! hh using 1
      · ext y
        change U y = ‖y‖ ^ 2 + Real.sqrt (1 - ‖y‖ ^ 2) + (1 / 32 : ℝ) * y 0
        dsimp only [U]
        ring
      · ext w
        simp only [add_apply, smul_apply, neg_apply, smul_eq_mul, innerSL_apply_apply]
        dsimp only [A]
        field_simp [hspos.ne']
        ring
    have hA : A = 2 - 1 / ws := by
      dsimp only [A]
      rw [hvsroot]
    have hcoef : (2 - 1 / ws) * (-Real.sqrt (1 - ws ^ 2)) + 1 / 32 = 0 := by
      nlinarith only [hwsroot]
    rw [hfirst.fderiv]
    ext w
    simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, zero_apply]
    have hinner : ⟪vs, w⟫_ℝ = (-Real.sqrt (1 - ws ^ 2)) * w 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct, Fin.sum_univ_two, star_trivial]
      change w 0 * (-Real.sqrt (1 - ws ^ 2)) + w 1 * 0 = _
      ring
    change A * ⟪vs, w⟫_ℝ + (1 / 32 : ℝ) * w 0 = 0
    rw [hA, hinner]
    calc
      _ = ((2 - 1 / ws) * (-Real.sqrt (1 - ws ^ 2)) + 1 / 32) * w 0 := by ring
      _ = 0 := by rw [hcoef, zero_mul]
  have hqscrit : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H qs = 0 := by
    apply (hcritiff qs hqspos).2
    simpa only [pi, hqscoord] using hvscrit
  have hqmcrit : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H qm = 0 := by
    apply (hcritiff qm hqmpos).2
    simpa only [pi, hqmcoord] using hvmcrit
  have hnative (q : UnitTwoSphere) (hq : (17 : ℝ) / 16 < H q - d) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H q = 0 ↔ q = qs ∨ q = qm := by
    have hz := hhigh q hq
    obtain ⟨hv, hupq, hh⟩ := hupper q hz
    constructor
    · intro hzero
      have hUv : (17 : ℝ) / 16 < U (pi q) := by linarith only [hq, hh]
      rcases hclass (pi q) (mem_ball_zero_iff.mpr hv) hUv
        ((hcritiff q hz).1 hzero) with hs | hm
      · left
        exact hupq.symm.trans (congrArg up hs)
      · right
        exact hupq.symm.trans (congrArg up hm)
    · rintro (rfl | rfl)
      · exact hqscrit
      · exact hqmcrit
  have hregular (q : UnitTwoSphere) (hq : (17 : ℝ) / 16 < H q - d)
      (hks : H q ≠ k + d) (hmu : H q ≠ mu + d) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H q ≠ 0 := by
    intro hzero
    rcases (hnative q hq).1 hzero with rfl | rfl
    · exact hks hHqs
    · exact hmu hHqm
  refine ⟨hH, hklo, hkhi, hmulo, hqscoord, hqmcoord, hHqs, hHqm, ?_, hregular, ?_⟩
  · intro q hq
    have hz := hhigh q hq
    exact ⟨hz, (hupper q hz).1, (hupper q hz).2.2, hnative q hq⟩
  · intro a b hab q hq
    change ((17 : ℝ) / 16 < a ∧ b < k) ∨ (k < a ∧ b < mu) at hab
    change H q ∈ Icc (a + d) (b + d) at hq
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · apply hregular q (by linarith only [ha, hq.1])
      · intro he
        linarith only [he, hb, hq.2]
      · intro he
        linarith only [he, hb, hkhi, hmulo, hq.2]
    · apply hregular q (by linarith only [hklo, ha, hq.1])
      · intro he
        linarith only [he, ha, hq.1]
      · intro he
        linarith only [he, hb, hq.2]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
