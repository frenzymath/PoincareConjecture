import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_BoundaryNormal
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology ContDiff Matrix

namespace PoincareConjecture

theorem m64Intrinsic_exists_signed_normal_collar
    {e : AnnulusCoordinates → AnnulusCoordinates} (he : ContDiff ℝ ∞ e)
    (hbase : ∀ p, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    {a : ℝ} (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 a)
      (deriv (fun t => e !₂[a, t]) 0))
    {O : Set AnnulusCoordinates} (hO : IsOpen O) (haO : !₂[a, 0] ∈ O) :
    ∃ epsilon > (0 : ℝ), ∃ W : Set ℝ, IsOpen W ∧ a ∈ W ∧
      ∀ p ∈ W, ∀ t ∈ Icc (-epsilon) epsilon,
        !₂[p, t] ∈ O ∧ ‖e !₂[p, t]‖ < 2 ∧
        (t < 0 → ‖e !₂[p, t]‖ < 1) ∧ (0 < t → 1 < ‖e !₂[p, t]‖) := by
  let u : ℝ × ℝ → AnnulusCoordinates := fun z => e !₂[z.1, z.2]
  have hpair : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (!₂[z.1, z.2] : AnnulusCoordinates)) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_snd
  have hu : ContDiff ℝ ∞ u := he.comp hpair
  let f : ℝ × ℝ → ℝ := fun z => ‖u z‖ ^ 2
  have hf : ContDiff ℝ ∞ f := (contDiff_norm_sq ℝ).comp hu
  let D : ℝ × ℝ → ℝ := fun z => fderiv ℝ f z (0, 1)
  have hD : Continuous D := (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hd (p t : ℝ) : HasDerivAt (fun s => f (p, s)) (D (p, t)) t :=
    (hf.differentiable (by simp) (p, t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t p).prodMk (hasDerivAt_id t))
  have hnormal : ContDiff ℝ ∞ (fun t => u (a, t)) := hu.comp (by fun_prop)
  have hD0 : 0 < D (a, 0) := by
    have heq := (hd a 0).unique ((hnormal.differentiable (by simp) 0).hasDerivAt.norm_sq)
    rw [heq]
    change 0 < 2 * inner ℝ (e !₂[a, 0]) (deriv (fun t => e !₂[a, t]) 0)
    rw [hbase]
    exact mul_pos (by norm_num) hinward
  let V : Set (ℝ × ℝ) :=
    {z | !₂[z.1, z.2] ∈ O} ∩ {z | 0 < D z} ∩ {z | ‖u z‖ < 2}
  have hV : IsOpen V :=
    ((hO.preimage hpair.continuous).inter (isOpen_lt continuous_const hD)).inter
      (isOpen_lt hu.continuous.norm continuous_const)
  have haV : (a, 0) ∈ V := by
    refine ⟨⟨haO, hD0⟩, ?_⟩
    change ‖e !₂[a, 0]‖ < 2
    rw [hbase]
    have hn := m64Intrinsic_boundary_self_inner 1 a
    rw [real_inner_self_eq_norm_sq] at hn
    nlinarith [norm_nonneg (intrinsicAnnulusBoundary 1 a)]
  obtain ⟨d, hdpos, hball⟩ := Metric.isOpen_iff.mp hV (a, 0) haV
  have hhalf : 0 < d / 2 := by positivity
  have hrectangle (p : ℝ) (hp : p ∈ ball a (d / 2))
      (t : ℝ) (ht : t ∈ Icc (-(d / 2)) (d / 2)) : (p, t) ∈ V := by
    apply hball
    simp only [mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs]
    exact max_lt ((mem_ball.mp hp).trans (by linarith only [hdpos]))
      ((abs_le.mpr ht).trans_lt (by linarith only [hdpos]))
  refine ⟨d / 2, hhalf, ball a (d / 2), isOpen_ball, mem_ball_self hhalf, ?_⟩
  intro p hp t ht
  have hhere := hrectangle p hp t ht
  have hmono : StrictMonoOn (fun s => f (p, s)) (Icc (-(d / 2)) (d / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hf.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    intro s hs
    change 0 < deriv (fun t => f (p, t)) s
    rw [(hd p s).deriv]
    exact (hrectangle p hp s (interior_subset hs)).1.2
  have hz : (0 : ℝ) ∈ Icc (-(d / 2)) (d / 2) := ⟨by linarith, hhalf.le⟩
  have hzero : f (p, 0) = 1 := by
    change ‖e !₂[p, 0]‖ ^ 2 = 1
    rw [hbase]
    have hn := m64Intrinsic_boundary_self_inner 1 p
    simpa only [real_inner_self_eq_norm_sq, one_pow] using hn
  refine ⟨hhere.1.1, hhere.2, ?_, ?_⟩
  · intro htneg
    have h := hmono ht hz htneg
    change f (p, t) < f (p, 0) at h
    rw [hzero] at h
    change ‖e !₂[p, t]‖ ^ 2 < 1 at h
    nlinarith [norm_nonneg (e !₂[p, t])]
  · intro htpos
    have h := hmono hz ht htpos
    change f (p, 0) < f (p, t) at h
    rw [hzero] at h
    change 1 < ‖e !₂[p, t]‖ ^ 2 at h
    nlinarith [norm_nonneg (e !₂[p, t])]

end PoincareConjecture
