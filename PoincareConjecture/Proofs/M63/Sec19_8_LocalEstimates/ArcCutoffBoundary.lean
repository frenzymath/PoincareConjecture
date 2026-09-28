import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ArcCutoffSpatial
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded











set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

open M62



theorem exists_m63ArcCutoff_profile :
    ∃ psi : ℝ → ℝ, ∃ P1 P2 : ℝ,
      0 ≤ P1 ∧ 0 ≤ P2 ∧ ContDiff ℝ ∞ psi ∧
      (∀ z, 0 ≤ psi z ∧ psi z ≤ 1) ∧
      (∀ z, |z| ≤ (3 / 8 : ℝ) → psi z = 1) ∧
      tsupport psi ⊆ Set.Ioo (-(9 / 20 : ℝ)) (9 / 20 : ℝ) ∧
      (∀ z, |deriv psi z| ≤ P1) ∧
      (∀ z, |deriv (deriv psi) z| ≤ P2) := by
  let f : ContDiffBump (0 : ℝ) :=
    { rIn := 3 / 8
      rOut := 7 / 16
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hf : ContDiff ℝ ∞ (f : ℝ → ℝ) := f.contDiff
  have hd1 := (contDiff_infty_iff_deriv.mp hf).2
  have hd2 := (contDiff_infty_iff_deriv.mp hd1).2
  obtain ⟨P1, hP1⟩ := hd1.continuous.bounded_above_of_compact_support
    f.hasCompactSupport.deriv
  obtain ⟨P2, hP2⟩ := hd2.continuous.bounded_above_of_compact_support
    f.hasCompactSupport.deriv.deriv
  have hP1abs (z : ℝ) : |deriv (f : ℝ → ℝ) z| ≤ P1 := by
    simpa only [Real.norm_eq_abs] using hP1 z
  have hP2abs (z : ℝ) : |deriv (deriv (f : ℝ → ℝ)) z| ≤ P2 := by
    simpa only [Real.norm_eq_abs] using hP2 z
  refine ⟨f, P1, P2, (abs_nonneg _).trans (hP1abs 0),
    (abs_nonneg _).trans (hP2abs 0), hf, ?_, ?_, ?_, hP1abs, hP2abs⟩
  · intro z
    exact ⟨f.nonneg, f.le_one⟩
  · intro z hz
    apply f.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, f] using hz
  · intro z hz
    rw [f.tsupport_eq] at hz
    have habs : |z| ≤ (7 / 16 : ℝ) := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, f] using hz
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    exact ⟨by linarith, by linarith⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)



theorem m63ArcCutoff_contDiff_two (hc : M62ShrinkingCurve F c)
    {t : ℝ} (ht : t ∈ Set.Icc a b) (x0 r : ℝ)
    (psi : ℝ → ℝ) (hpsi : ContDiff ℝ 2 psi) :
    ContDiff ℝ 2 (fun x => psi (m63ArcLength F c t x0 x / r)) := by
  have hv : ContDiff ℝ 1 (curveSpeed F c t) := speed_contDiff F c hc ht
  let sigma := fun x => m63ArcLength F c t x0 x
  have hsigma (x : ℝ) : HasDerivAt sigma (curveSpeed F c t x) x :=
    (hv.continuous.integral_hasStrictDerivAt x0 x).hasDerivAt
  have heq : deriv sigma = curveSpeed F c t := funext fun x => (hsigma x).deriv
  have hsmooth : ContDiff ℝ 2 sigma := by
    change ContDiff ℝ ((1 : ℕ∞ω) + 1) sigma
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x => (hsigma x).differentiableAt, by simp, ?_⟩
    rw [heq]
    exact hv
  exact hpsi.comp (hsmooth.div_const r)




theorem m63ArcCutoff_boundary_zero (hc : M62ShrinkingCurve F c)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (hr : 0 < r) (alpha beta x0 : ℝ)
    (psi : ℝ → ℝ) (hpsi : ContDiff ℝ 2 psi)
    (hSupport : tsupport psi ⊆ Set.Ioo (-(9 / 20 : ℝ)) (9 / 20 : ℝ))
    (hLeft : (9 / 20 : ℝ) * r ≤ m63ArcLength F c t alpha x0)
    (hRight : (9 / 20 : ℝ) * r ≤ m63ArcLength F c t x0 beta) :
    psi (m63ArcLength F c t x0 alpha / r) = 0 ∧
      psi (m63ArcLength F c t x0 beta / r) = 0 ∧
      m62ArcDerivative F c t (fun y => psi (m63ArcLength F c t x0 y / r)) alpha = 0 ∧
      m62ArcDerivative F c t (fun y => psi (m63ArcLength F c t x0 y / r)) beta = 0 := by
  have hrev : m63ArcLength F c t x0 alpha = -m63ArcLength F c t alpha x0 :=
    intervalIntegral.integral_symm alpha x0
  have hleft : m63ArcLength F c t x0 alpha / r ≤ -(9 / 20 : ℝ) := by
    apply (div_le_iff₀ hr).mpr
    rw [hrev]
    nlinarith only [hLeft]
  have hright : (9 / 20 : ℝ) ≤ m63ArcLength F c t x0 beta / r :=
    (le_div_iff₀ hr).mpr hRight
  have hleftOut : m63ArcLength F c t x0 alpha / r ∉ tsupport psi := by
    intro hmem
    exact (not_lt_of_ge hleft) (hSupport hmem).1
  have hrightOut : m63ArcLength F c t x0 beta / r ∉ tsupport psi := by
    intro hmem
    exact (not_lt_of_ge hright) (hSupport hmem).2
  refine ⟨image_eq_zero_of_notMem_tsupport hleftOut,
    image_eq_zero_of_notMem_tsupport hrightOut, ?_, ?_⟩
  · rw [(m63ArcCutoff_spatial_derivatives F c hc ht hr x0 alpha psi hpsi).2.1,
      deriv_of_notMem_tsupport hleftOut, zero_div]
  · rw [(m63ArcCutoff_spatial_derivatives F c hc ht hr x0 beta psi hpsi).2.1,
      deriv_of_notMem_tsupport hrightOut, zero_div]

end PoincareConjecture
