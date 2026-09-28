import PoincareConjecture.Proofs.M04.ScalarChainRule
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic








set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M04

private noncomputable def cutoffRoot (s : ℝ) : ℝ := Real.smoothTransition (2 - 2 * s)

noncomputable def shiCutoffProfile (s : ℝ) : ℝ := cutoffRoot s ^ 2

private theorem cutoffRoot_smooth : ContDiff ℝ ∞ cutoffRoot :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))

theorem shiCutoffProfile_smooth : ContDiff ℝ ∞ shiCutoffProfile := cutoffRoot_smooth.pow 2

private theorem cutoffRoot_nonneg (s : ℝ) : 0 ≤ cutoffRoot s :=
  Real.smoothTransition.nonneg _

private theorem cutoffRoot_le_one (s : ℝ) : cutoffRoot s ≤ 1 :=
  Real.smoothTransition.le_one _

private theorem cutoffRoot_one {s : ℝ} (hs : s ≤ 1 / 2) : cutoffRoot s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem cutoffRoot_zero {s : ℝ} (hs : 1 ≤ s) : cutoffRoot s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem cutoffRoot_antitone : Antitone cutoffRoot := by
  intro s t hst
  exact Real.smoothTransition.monotone (by linarith)

theorem shiCutoffProfile_mem_Icc (s : ℝ) : shiCutoffProfile s ∈ Icc 0 1 := by
  constructor
  · exact sq_nonneg _
  · have h0 := cutoffRoot_nonneg s
    have h1 := cutoffRoot_le_one s
    dsimp [shiCutoffProfile]
    nlinarith

theorem shiCutoffProfile_one {s : ℝ} (hs : s ≤ 1 / 2) : shiCutoffProfile s = 1 := by
  simp only [shiCutoffProfile, cutoffRoot_one hs, one_pow]

theorem shiCutoffProfile_zero {s : ℝ} (hs : 1 ≤ s) : shiCutoffProfile s = 0 := by
  simp only [shiCutoffProfile, cutoffRoot_zero hs, zero_pow (by decide : 2 ≠ 0)]

theorem shiCutoffProfile_antitone : Antitone shiCutoffProfile := by
  intro s t hst
  exact (sq_le_sq₀ (cutoffRoot_nonneg t) (cutoffRoot_nonneg s)).2
    (cutoffRoot_antitone hst)

private theorem const_germ_outside {f : ℝ → ℝ} {c₀ c₁ : ℝ}
    (hleft : ∀ x ≤ 0, f x = c₀) (hright : ∀ x, 1 ≤ x → f x = c₁)
    {x : ℝ} (hx : x ∉ Icc 0 1) :
    ∃ c : ℝ, f =ᶠ[𝓝 x] (fun _ => c) := by
  by_cases hx0 : x < 0
  · refine ⟨c₀, ?_⟩
    filter_upwards [gt_mem_nhds hx0] with y hy
    exact hleft y hy.le
  · have hx1 : 1 < x := lt_of_not_ge (fun hx1 => hx ⟨le_of_not_gt hx0, hx1⟩)
    refine ⟨c₁, ?_⟩
    filter_upwards [lt_mem_nhds hx1] with y hy
    exact hright y hy.le

private theorem deriv_bounds_of_plateaus {f : ℝ → ℝ} {c₀ c₁ : ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hleft : ∀ x ≤ 0, f x = c₀) (hright : ∀ x, 1 ≤ x → f x = c₁) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      (∀ x, |deriv f x| ≤ B) ∧ (∀ x, |deriv (deriv f) x| ≤ C) := by
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hf'' : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hf').2
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf'.continuous.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf''.continuous.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨max 1 B, max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have hxb : |deriv f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x hx
      exact hxb.trans (le_max_right _ _)
    · obtain ⟨c, hc⟩ := const_germ_outside hleft hright hx
      rw [hc.deriv_eq, deriv_const, abs_zero]
      exact (zero_le_one.trans (le_max_left _ _))
  · intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have hxc : |deriv (deriv f) x| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC x hx
      exact hxc.trans (le_max_right _ _)
    · obtain ⟨c, hc⟩ := const_germ_outside hleft hright hx
      have hd : deriv f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hc.deriv] with y hy
        simpa only [deriv_const] using hy
      rw [hd.deriv_eq, deriv_const, abs_zero]
      exact (zero_le_one.trans (le_max_left _ _))

theorem exists_shiCutoffProfile_bounds :
    ∃ C₁ C₂ G : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < G ∧
      ∀ s : ℝ, -C₁ ≤ deriv shiCutoffProfile s ∧ deriv shiCutoffProfile s ≤ 0 ∧
        |deriv (deriv shiCutoffProfile) s| ≤ C₂ ∧
        (deriv shiCutoffProfile s) ^ 2 ≤ G * shiCutoffProfile s := by
  obtain ⟨B, _, hB, _, hBbound, _⟩ := deriv_bounds_of_plateaus cutoffRoot_smooth
    (fun x hx => cutoffRoot_one (by linarith)) (fun _ hx => cutoffRoot_zero hx)
  obtain ⟨C₁, C₂, hC₁, hC₂, hfirst, hsecond⟩ := deriv_bounds_of_plateaus
    shiCutoffProfile_smooth (fun x hx => shiCutoffProfile_one (by linarith))
    (fun _ hx => shiCutoffProfile_zero hx)
  refine ⟨C₁, C₂, 4 * B ^ 2, hC₁, hC₂, by positivity, ?_⟩
  intro s
  refine ⟨(abs_le.mp (hfirst s)).1, shiCutoffProfile_antitone.deriv_nonpos,
    hsecond s, ?_⟩
  have hd : deriv shiCutoffProfile s = 2 * cutoffRoot s * deriv cutoffRoot s := by
    rw [show shiCutoffProfile = cutoffRoot ^ 2 from rfl]
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      ((cutoffRoot_smooth.differentiable (by simp) s).hasDerivAt.pow 2).deriv
  have hsq : (deriv cutoffRoot s) ^ 2 ≤ B ^ 2 := by
    nlinarith [sq_abs (deriv cutoffRoot s), hBbound s, abs_nonneg (deriv cutoffRoot s)]
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * cutoffRoot s ^ 2 by positivity)
  rw [hd]
  dsimp only [shiCutoffProfile]
  nlinarith only [hm]

private theorem profile_scaled_deriv (b s : ℝ) :
    deriv (fun r => shiCutoffProfile (b * r)) s = b * deriv shiCutoffProfile (b * s) := by
  have h := (shiCutoffProfile_smooth.differentiable (by simp) (b * s)).hasDerivAt.comp s
    ((hasDerivAt_id s).const_mul b)
  simpa only [Function.comp_def, mul_one, mul_comm] using h.deriv

private theorem profile_scaled_second_deriv (b s : ℝ) :
    deriv (deriv (fun r => shiCutoffProfile (b * r))) s =
      b ^ 2 * deriv (deriv shiCutoffProfile) (b * s) := by
  have he : deriv (fun r => shiCutoffProfile (b * r)) =
      fun r => b * deriv shiCutoffProfile (b * r) := funext (profile_scaled_deriv b)
  rw [he]
  have hd : ContDiff ℝ ∞ (deriv shiCutoffProfile) :=
    (contDiff_infty_iff_deriv.mp shiCutoffProfile_smooth).2
  have h := ((hd.differentiable (by simp) (b * s)).hasDerivAt.comp s
    ((hasDerivAt_id s).const_mul b)).const_mul b
  convert! h.deriv using 1; ring

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in
theorem shiCutoffProfile_gradient_comp
    (g : RiemannianMetric n M) {U : Set M} {u : M → ℝ}
    (hU : IsOpen U) (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U)
    {x : M} (hx : x ∈ U) (b : ℝ) :
    scalarGradientSq g (fun y => shiCutoffProfile (b * u y)) x =
      b ^ 2 * (deriv shiCutoffProfile (b * u x)) ^ 2 * scalarGradientSq g u x := by
  let φ := fun s => shiCutoffProfile (b * s)
  have hφ : ContDiff ℝ ∞ φ :=
    shiCutoffProfile_smooth.comp (contDiff_const.mul contDiff_id)
  have hud := (hu.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdir (v : TangentSpace (𝓡 n) x) :
      mvfderiv (𝓡 n) (fun y => shiCutoffProfile (b * u y)) x v =
        (b * deriv shiCutoffProfile (b * u x)) * mvfderiv (𝓡 n) u x v := by
    calc
      _ = deriv φ (u x) * mvfderiv (𝓡 n) u x v := by
        change mvfderiv (𝓡 n) (φ ∘ u) x v = _
        rw [mvfderiv_comp_apply x
          ((hφ.differentiable (by simp)) (u x)).mdifferentiableAt hud v]
        simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
        exact fderiv_eq_deriv_mul (𝕜 := ℝ)
      _ = _ := by rw [profile_scaled_deriv]
  unfold scalarGradientSq
  simp only [hdir, mul_pow, ← Finset.mul_sum]

theorem shiCutoffProfile_laplacian_comp
    (D : LeviCivitaData g) {U : Set M} {u : M → ℝ}
    (hU : IsOpen U) (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U)
    {x : M} (hx : x ∈ U) (b : ℝ) :
    D.laplacian (fun y => shiCutoffProfile (b * u y)) x =
      b * deriv shiCutoffProfile (b * u x) * D.laplacian u x +
        b ^ 2 * deriv (deriv shiCutoffProfile) (b * u x) * scalarGradientSq g u x := by
  have hφ : ContDiff ℝ ∞ (fun s => shiCutoffProfile (b * s)) :=
    shiCutoffProfile_smooth.comp (contDiff_const.mul contDiff_id)
  have h := laplacian_comp D hU hu hφ hx
  rw [profile_scaled_deriv, profile_scaled_second_deriv] at h
  exact h

set_option maxHeartbeats 800000 in

theorem shiCutoffProfile_composition_bounds
    (D : LeviCivitaData g) {U : Set M} {u : M → ℝ}
    (hU : IsOpen U) (hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U)
    {x : M} (hx : x ∈ U) {b κ ε C₁ C₂ G : ℝ}
    (hb : 0 < b) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hG : 0 ≤ G)
    (hprofile : -C₁ ≤ deriv shiCutoffProfile (b * u x) ∧
      deriv shiCutoffProfile (b * u x) ≤ 0 ∧
      |deriv (deriv shiCutoffProfile) (b * u x)| ≤ C₂ ∧
      (deriv shiCutoffProfile (b * u x)) ^ 2 ≤ G * shiCutoffProfile (b * u x))
    (hd : 0 < u x) (hhalf : 1 / 2 ≤ b * u x) (hone : b * u x ≤ 1)
    (hgrad : scalarGradientSq g u x ≤ 1)
    (hlap : D.laplacian u x ≤ (n : ℝ) / u x + κ * u x + ε) :
    scalarGradientSq g (fun y => shiCutoffProfile (b * u y)) x ≤
        G * b ^ 2 * shiCutoffProfile (b * u x) ∧
      -D.laplacian (fun y => shiCutoffProfile (b * u y)) x ≤
        (2 * (n : ℝ) * C₁ + C₂) * b ^ 2 + C₁ * κ + C₁ * b * ε := by
  have hgrad0 : 0 ≤ scalarGradientSq g u x :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp0 := (shiCutoffProfile_mem_Icc (b * u x)).1
  constructor
  · rw [shiCutoffProfile_gradient_comp g hU hu hx b]
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprofile.2.2.2 (sq_nonneg b)) hgrad0
    have h2 := mul_le_mul_of_nonneg_left hgrad
      (show 0 ≤ b ^ 2 * (G * shiCutoffProfile (b * u x)) by positivity)
    nlinarith only [h1, h2]
  · rw [shiCutoffProfile_laplacian_comp D hU hu hx b]
    have hA0 : 0 ≤ -(b * deriv shiCutoffProfile (b * u x)) :=
      neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hb.le hprofile.2.1)
    have hA1 : -(b * deriv shiCutoffProfile (b * u x)) ≤ b * C₁ := by
      have h := mul_le_mul_of_nonneg_left hprofile.1 hb.le
      linarith
    have hR : 0 ≤ (n : ℝ) / u x + κ * u x + ε := by positivity
    have h1 := (mul_le_mul_of_nonneg_left hlap hA0).trans
      (mul_le_mul_of_nonneg_right hA1 hR)
    have hsecond : -deriv (deriv shiCutoffProfile) (b * u x) ≤ C₂ := by
      linarith [(abs_le.mp hprofile.2.2.1).1]
    have h2a := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsecond (sq_nonneg b)) hgrad0
    have h2b := mul_le_mul_of_nonneg_left hgrad (mul_nonneg (sq_nonneg b) hC₂)
    have hratio : b / u x ≤ 2 * b ^ 2 := by
      apply (div_le_iff₀ hd).2
      have h := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2 * b by positivity)
      nlinarith only [h]
    have hn : b * C₁ * ((n : ℝ) / u x) ≤ 2 * (n : ℝ) * C₁ * b ^ 2 := by
      calc
        _ = ((n : ℝ) * C₁) * (b / u x) := by ring
        _ ≤ ((n : ℝ) * C₁) * (2 * b ^ 2) :=
          mul_le_mul_of_nonneg_left hratio (mul_nonneg (Nat.cast_nonneg _) hC₁)
        _ = _ := by ring
    have hk := mul_le_mul_of_nonneg_left hone (mul_nonneg hC₁ hκ)
    nlinarith only [h1, h2a, h2b, hn, hk]

end PoincareConjecture.M04

