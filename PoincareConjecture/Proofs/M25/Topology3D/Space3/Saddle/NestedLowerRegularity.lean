import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedLowerRoots
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SouthernSphereChart
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem height_regular (d : ℝ) (q : UnitTwoSphere)
    (hq : (heightCoordinates
      (nestedReferenceDiffeomorph d (q : E3))).2 = 17 / 16 + d) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere =>
        (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2)
      q ≠ 0 := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let H : ℝ := 17 / 16
  let U : ℝ → ℝ → ℝ := fun t r =>
    r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
  let D : ℝ → ℝ → ℝ := fun t r =>
    2 * r - r / Real.sqrt (1 - r ^ 2) + t / 32
  let f : UnitTwoSphere → ℝ := fun p =>
    (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    contDiff_snd.contMDiff.comp (heightCoordinates.contDiff.contMDiff.comp
      ((nestedReferenceDiffeomorph d).contMDiff_toFun.comp contMDiff_coe_sphere))
  have hNorm (v : E2) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hformula (p : UnitTwoSphere) : f p =
      ‖(heightCoordinates (p : E3)).1‖ ^ 2 + (heightCoordinates (p : E3)).2 +
        (heightCoordinates (p : E3)).1 0 / 32 + d := by
    dsimp only [f]
    rw [(nestedReferenceDiffeomorph_apply_symm d).1 (p : E3),
      heightCoordinates_snd_apply, hNorm]
    change (p : E3) 2 + (p : E3) 0 ^ 2 + (p : E3) 1 ^ 2 + (p : E3) 0 / 32 + d =
      ((p : E3) 0 ^ 2 + (p : E3) 1 ^ 2) + (p : E3) 2 + (p : E3) 0 / 32 + d
    ring
  let v := (heightCoordinates (q : E3)).1
  let z := (heightCoordinates (q : E3)).2
  let r := ‖v‖
  have hsphere : r ^ 2 + z ^ 2 = 1 := sphere_height_coordinates_sq q
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ 1 := by nlinarith only [hsphere, hr0, sq_nonneg z]
  have hvcoord : v 0 ≤ r := by
    have hh := hNorm v
    change r ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 at hh
    nlinarith only [hh, hr0, sq_nonneg (v 1)]
  have hheight : r ^ 2 + z + v 0 / 32 = H := by
    have hh : f q = H + d := hq
    rw [hformula] at hh
    change r ^ 2 + z + v 0 / 32 + d = H + d at hh
    linarith only [hh]
  have hz : 0 < z := by
    by_contra h
    have hn : z ≤ 0 := le_of_not_gt h
    have hrsq : r ^ 2 ≤ 1 := by nlinarith only [hsphere, sq_nonneg z]
    dsimp only [H] at hheight
    linarith only [hheight, hn, hrsq, hvcoord, hr1]
  have hrlt : r < 1 := by nlinarith only [hsphere, hr0, pow_pos hz 2]
  have hr : 0 < r := by
    by_contra h
    have hrz : r = 0 := le_antisymm (le_of_not_gt h) hr0
    have hvz : v = 0 := norm_eq_zero.mp hrz
    have hv0 : v 0 = 0 := congrArg (fun p : E2 => p 0) hvz
    rw [hrz, hv0] at hheight
    rw [hrz] at hsphere
    dsimp only [H] at hheight
    nlinarith only [hsphere, hheight, hz]
  have hsqrt : Real.sqrt (1 - r ^ 2) = z := by
    rw [show 1 - r ^ 2 = z ^ 2 by linarith only [hsphere],
      Real.sqrt_sq_eq_abs, abs_of_pos hz]
  let u : E2 := r⁻¹ • v
  have hu : ‖u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hru : r • u = v := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hru0 : r * u 0 = v 0 := congrArg (fun p : E2 => p 0) hru
  have hut : u 0 ∈ Ioo (-3 / 2 : ℝ) (3 / 2) := by
    have hh := hNorm u
    rw [hu] at hh
    constructor <;> nlinarith only [hh, sq_nonneg (u 1)]
  have hroot : U (u 0) r = H := by
    change r ^ 2 + Real.sqrt (1 - r ^ 2) + r * u 0 / 32 = H
    rw [hsqrt, hru0]
    exact hheight
  obtain ⟨ri, ro, _hri, _hro, hroots⟩ := exists_smooth_roots
  have hrt := hroots (u 0) hut
  have hchoice : r = ri (u 0) ∨ r = ro (u 0) :=
    (hrt.2.2.2.2.2.2.1 r ⟨hr.le, hrlt.le⟩).1.mp hroot
  have hnonzero : D (u 0) r ≠ 0 := by
    rcases hchoice with hri | hro
    · rw [hri]
      have hh := hrt.2.2.2.2.2.2.2.1
      have hpos : 0 < D (u 0) (ri (u 0)) := by
        dsimp only [D]
        linarith only [hh]
      exact ne_of_gt hpos
    · rw [hro]
      have hh := hrt.2.2.2.2.2.2.2.2
      have hneg : D (u 0) (ro (u 0)) < 0 := by
        dsimp only [D]
        linarith only [hh]
      exact ne_of_lt hneg
  let up : E2 → UnitTwoSphere := fun x => -southSpherePoint (-x)
  have hupCoordinates (x : E2) (hx : ‖x‖ < 1) :
      heightCoordinates (up x : E3) = (x, Real.sqrt (1 - ‖x‖ ^ 2)) := by
    change heightCoordinates ((-southSpherePoint (-x) : UnitTwoSphere) : E3) = _
    rw [coe_neg_sphere, map_neg,
      southSpherePoint_coordinates (-x) (by simpa only [norm_neg] using hx), norm_neg]
    change (-(-x), -(-Real.sqrt (1 - ‖x‖ ^ 2))) =
      (x, Real.sqrt (1 - ‖x‖ ^ 2))
    simp only [neg_neg]
  have hupSmooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ up (ball (0 : E2) 1) := by
    have hneg : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E2) ∞
        (fun x : E2 => -x) (ball (0 : E2) 1) :=
      contDiff_id.neg.contMDiff.contMDiffOn
    exact contMDiff_neg_sphere.comp_contMDiffOn
      (southSpherePoint_contMDiffOn.comp hneg (fun x hx => by
        change -x ∈ ball (0 : E2) 1
        simpa only [mem_ball_zero_iff, norm_neg] using hx))
  let gamma : ℝ → UnitTwoSphere := fun s => up (s • u)
  have hscale (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : ‖s • u‖ = s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1, hu, mul_one]
  have hgammaCoordinates (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      heightCoordinates (gamma s : E3) = (s • u, Real.sqrt (1 - s ^ 2)) := by
    rw [hupCoordinates _ (by rw [hscale s hs]; exact hs.2), hscale s hs]
  have hgamma : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ gamma r := by
    have harg : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) ∞
        (fun s : ℝ => s • u) r :=
      (contDiff_id.smul contDiff_const).contMDiff.contMDiffAt
    have hup : ContMDiffAt 𝓘(ℝ, E2) (𝓡 2) ∞
        (fun x : E2 => -southSpherePoint (-x)) (r • u) := by
      simpa only [up] using hupSmooth.contMDiffAt
        (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by
          rw [hscale r ⟨hr, hrlt⟩]
          exact hrlt)))
    have hcomp := hup.comp r harg
    simpa only [gamma, Function.comp_def] using hcomp
  have hgammaq : gamma r = q := by
    apply Subtype.ext
    apply heightCoordinates.injective
    rw [hgammaCoordinates r ⟨hr, hrlt⟩, hru, hsqrt]
  have hlocal : (f ∘ gamma) =ᶠ[𝓝 r] fun s => U (u 0) s + d := by
    filter_upwards [Ioo_mem_nhds hr hrlt] with s hs
    change f (gamma s) = _
    rw [hformula, hgammaCoordinates s hs]
    change ‖s • u‖ ^ 2 + Real.sqrt (1 - s ^ 2) + (s • u) 0 / 32 + d = _
    rw [hscale s hs]
    rfl
  have hd : HasDerivAt (f ∘ gamma) (D (u 0) r) r := by
    obtain ⟨_, _, _, _, hder, _⟩ := radial_estimates
    have hd0 := (hder (u 0) r ⟨by linarith only [hr], hrlt⟩).add_const d
    exact hd0.congr_of_eventuallyEq hlocal
  intro hzero
  have hc := mfderiv_comp r (hf.mdifferentiable (by simp) (gamma r))
    (hgamma.mdifferentiableAt (by simp))
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ gamma) r : ℝ →L[ℝ] ℝ) =
    (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (gamma r) : E2 →L[ℝ] ℝ).comp
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) gamma r : ℝ →L[ℝ] E2) at hc
  have hz' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (gamma r) = 0 := hgammaq.symm ▸ hzero
  rw [hz', ContinuousLinearMap.zero_comp] at hc
  have hm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ gamma) r =
      ContinuousLinearMap.toSpanSingleton ℝ (D (u 0) r) := hd.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hm] at hc
  have hh := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) hc
  apply hnonzero
  rw [ContinuousLinearMap.toSpanSingleton_apply_one] at hh
  exact hh

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
