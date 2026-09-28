import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnCutoff
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "K" => m64AnnulusDomain
local notation "a" => curvePeriod / 2
local notation "ei" i => EuclideanSpace.single (i : Fin 2) (1 : ℝ)

def m64HalfTurnBlend (j : ℕ) (f g : LoopPlane → ℝ) (p : LoopPlane) : ℝ :=
  f p + m64HalfTurnCutoff j p * (g p - f p)

def m64HalfTurnPiece (f g : LoopPlane → ℝ) (p : LoopPlane) : ℝ :=
  if p 0 < curvePeriod / 2 then f p else g p

theorem m64HalfTurnBlend_contDiff {f g : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (j : ℕ) :
    ContDiff ℝ 1 (m64HalfTurnBlend j f g) :=
  hf.add (((m64HalfTurnCutoff_contDiff j).of_le (by simp)).mul (hg.sub hf))

theorem m64HalfTurnBlend_fderiv {f g : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (j : ℕ) (p : LoopPlane) (i : Fin 2) :
    fderiv ℝ (m64HalfTurnBlend j f g) p (ei i) =
      fderiv ℝ f p (ei i) + m64HalfTurnCutoff j p *
        (fderiv ℝ g p (ei i) - fderiv ℝ f p (ei i)) +
          fderiv ℝ (m64HalfTurnCutoff j) p (ei i) * (g p - f p) := by
  rw [show m64HalfTurnBlend j f g =
      (fun q => f q + m64HalfTurnCutoff j q * (g q - f q)) from rfl]
  have hsub : DifferentiableAt ℝ (fun q => g q - f q) p :=
    (hg.differentiable (by simp) p).sub (hf.differentiable (by simp) p)
  have hmul : DifferentiableAt ℝ (fun q => m64HalfTurnCutoff j q * (g q - f q)) p :=
    ((m64HalfTurnCutoff_contDiff j).differentiable (by simp) p).mul hsub
  rw [fderiv_fun_add (hf.differentiable (by simp) p)
    hmul, fderiv_fun_mul ((m64HalfTurnCutoff_contDiff j).differentiable (by simp) p) hsub,
    fderiv_fun_sub (hg.differentiable (by simp) p) (hf.differentiable (by simp) p)]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

theorem m64HalfTurnBlend_eventually {f g : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {p : LoopPlane}
    (hp : p 0 ≠ a) (i : Fin 2) :
    ∀ᶠ j : ℕ in atTop,
      m64HalfTurnBlend j f g p = m64HalfTurnPiece f g p ∧
        fderiv ℝ (m64HalfTurnBlend j f g) p (ei i) =
          m64HalfTurnPiece (fun q => fderiv ℝ f q (ei i))
            (fun q => fderiv ℝ g q (ei i)) p := by
  filter_upwards [m64HalfTurnCutoff_eventually hp,
    m64HalfTurnCutoff_deriv_eventually hp i] with j hj hd
  rw [m64HalfTurnBlend_fderiv hf hg]
  simp only [m64HalfTurnBlend, hj, hd, zero_mul, add_zero, m64HalfTurnPiece]
  split_ifs <;> constructor <;> ring

theorem m64HalfTurnBlend_endpoints {f g : LoopPlane → ℝ} (j : ℕ) (s : ℝ) :
    m64HalfTurnBlend j f g (annulusPoint 0 s) = f (annulusPoint 0 s) ∧
      m64HalfTurnBlend j f g (annulusPoint curvePeriod s) =
        g (annulusPoint curvePeriod s) := by
  simp [m64HalfTurnBlend, (m64HalfTurnCutoff_endpoints j s).1,
    (m64HalfTurnCutoff_endpoints j s).2]

theorem m64HalfTurnBlend_bound {f g : LoopPlane → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j p, p ∈ K → |m64HalfTurnBlend j f g p| ≤ C := by
  obtain ⟨B, hB⟩ := m64AnnulusDomain_isCompact.exists_bound_of_continuousOn
    ((hf.norm.add hg.norm).continuousOn)
  refine ⟨max (3 * B) 0, le_max_right _ _, ?_⟩
  intro j p hp
  have hsum : |f p| + |g p| ≤ B := by
    have h := hB p hp
    change ‖‖f p‖ + ‖g p‖‖ ≤ B at h
    simp only [Real.norm_eq_abs] at h
    rwa [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at h
  have hχ := m64HalfTurnCutoff_bounds j p
  have hprod : |m64HalfTurnCutoff j p * (g p - f p)| ≤ |g p| + |f p| := by
    rw [abs_mul, abs_of_nonneg hχ.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) hχ.2).trans (abs_sub _ _)
  exact ((abs_add_le _ _).trans (by linarith [hprod, abs_nonneg (f p), abs_nonneg (g p)])).trans
    (le_max_left _ _)

theorem m64HalfTurn_matching_gap {f g : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hmatch : ∀ s ∈ Icc (0 : ℝ) 1, f (annulusPoint a s) = g (annulusPoint a s)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ K, |g p - f p| ≤ L * |p 0 - a| := by
  obtain ⟨L, hL⟩ := (hg.sub hf).contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : ℕ∞ω) ≠ 0) m64AnnulusDomain_convex m64AnnulusDomain_isCompact
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro p hp
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hq : annulusPoint a (p 1) ∈ K :=
    ⟨by change 0 ≤ curvePeriod / 2; positivity,
      by change curvePeriod / 2 ≤ curvePeriod; linarith, hp.2.2⟩
  have hnorm : ‖p - annulusPoint a (p 1)‖ = |p 0 - a| := by
    have heq : p - annulusPoint a (p 1) = EuclideanSpace.single (0 : Fin 2) (p 0 - a) := by
      ext i
      fin_cases i <;> simp [annulusPoint]
    rw [heq]
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_single 2 (fun _ : Fin 2 => ℝ) 0 (p 0 - a)
  have h := hL.dist_le_mul p hp (annulusPoint a (p 1)) hq
  simpa only [Pi.sub_apply, hmatch (p 1) hp.2.2, sub_self, Real.dist_eq,
    sub_zero, dist_eq_norm, hnorm, Real.norm_eq_abs] using h

theorem m64HalfTurnBlend_derivative_bound {f g : LoopPlane → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (i : Fin 2)
    (hmatch : i = 1 ∨
      ∀ s ∈ Icc (0 : ℝ) 1, f (annulusPoint a s) = g (annulusPoint a s)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j p, p ∈ K →
      |fderiv ℝ (m64HalfTurnBlend j f g) p (ei i)| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := m64HalfTurnBlend_bound
    ((hf.continuous_fderiv (by simp)).clm_apply (continuous_const (y := ei i)))
    ((hg.continuous_fderiv (by simp)).clm_apply (continuous_const (y := ei i)))
  have hextra : ∃ C : ℝ, 0 ≤ C ∧ ∀ j p, p ∈ K →
      |fderiv ℝ (m64HalfTurnCutoff j) p (ei i) * (g p - f p)| ≤ C := by
    rcases hmatch with rfl | hmatch
    · refine ⟨0, le_rfl, ?_⟩
      intro j p _
      norm_num [m64HalfTurnCutoff_fderiv]
    · obtain ⟨C, hC, hbound⟩ := m64SmoothTransition_deriv_bound
      obtain ⟨L, hL, hgap⟩ := m64HalfTurn_matching_gap hf hg hmatch
      refine ⟨C * L, mul_nonneg hC hL, ?_⟩
      intro j p hp
      fin_cases i
      · exact m64HalfTurnCutoff_matching_derivative_bound hC hL hbound j p (hgap p hp)
      · norm_num [m64HalfTurnCutoff_fderiv]
        exact mul_nonneg hC hL
  obtain ⟨C, hC, hc⟩ := hextra
  refine ⟨B + C, add_nonneg hB0 hC, ?_⟩
  intro j p hp
  rw [m64HalfTurnBlend_fderiv hf hg]
  exact (abs_add_le _ _).trans (add_le_add (hB j p hp) (hc j p hp))

end PoincareConjecture
