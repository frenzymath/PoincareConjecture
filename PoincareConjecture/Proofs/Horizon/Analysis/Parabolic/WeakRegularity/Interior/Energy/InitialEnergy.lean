




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.LocalMollified
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.KernelBuffer
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.WeakCompactExtension









open Set MeasureTheory Filter Metric
open Poincare.Analysis.Convolution
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Poincare.Analysis.Parabolic.WeakRegularity.Canonical

theorem exists_local_mollified_gradient_energy
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    (hEll : C.IsUniformlyEllipticOn U)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hw : WeakSolutionOn C u U) {z : Spacetime n} (hz : z ∈ U)
    {ρ : Spacetime n → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) :
    ∃ χ : ContDiffBump z, tsupport χ ⊆ U ∧
      ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
        (∫ y, ∑ i, (χ y * spatialDeriv i (mollifiedValue u ρ r) y) ^ 2) ≤ B := by
  obtain ⟨V, C', u', hV, hzV, hVU, hC', hpc, hbc, hcc, hu', huc,
    hpEq, hbEq, hcEq, huEq, hw'⟩ := exists_weak_compact_extension hU hC hu hw hz
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzV)
  let χ : ContDiffBump z :=
    { rIn := δ / 8
      rOut := δ / 4
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hχball : tsupport χ ⊆ ball z (δ / 2) := by
    rw [χ.tsupport_eq]
    intro y hy
    exact (mem_closedBall.mp hy).trans_lt (by change δ / 4 < δ / 2; linarith)
  have hKV : closedBall z (δ / 2) ⊆ V := by
    intro y hy
    exact hδV ((mem_closedBall.mp hy).trans_lt (by linarith))
  have hχV : tsupport χ ⊆ V := hχball.trans (ball_subset_closedBall.trans hKV)
  obtain ⟨ε, hε, hsupport⟩ := exists_uniform_translated_rescaledKernel_support_subset
    (isCompact_closedBall z (δ / 2)) hV hKV hρc
  obtain ⟨κ, hκ, hell⟩ := hEll
  have hprincipal : ∀ i j, ContDiff ℝ ∞ (C'.principal i j) :=
    fun i j => contDiffOn_univ.mp (hC'.1 i j)
  have hdrift : ∀ i, ContDiff ℝ ∞ (C'.drift i) :=
    fun i => contDiffOn_univ.mp (hC'.2.1 i)
  have hzeroth : ContDiff ℝ ∞ C'.zeroth := contDiffOn_univ.mp hC'.2.2
  have hEll' : ∀ y ∈ tsupport χ, ∀ ξ : Euclid n,
      κ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, C'.principal i j y * ξ i * ξ j := by
    intro y hy ξ
    simp_rw [hpEq _ _ (hχV hy)]
    exact hell y (hVU (hχV hy)) ξ
  obtain ⟨B, hB, henergy⟩ := exists_uniform_local_mollified_cutoff_gradient_bound
    hprincipal hpc hdrift hbc hzeroth hcc hu' huc hw'
    hρ hρc χ.contDiff χ.hasCompactSupport hκ hEll'
  refine ⟨χ, hχV.trans hVU, ε, B, hε, hB, ?_⟩
  intro r hr hrε
  have hconv : EqOn (mollifiedValue u' ρ r) (mollifiedValue u ρ r)
      (ball z (δ / 2)) := by
    intro w hwball
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ V
    · rw [huEq hy]
    · have he : rescaledKernel ρ r (w - y) = 0 :=
        image_eq_zero_of_notMem_tsupport (f := translatedKernel (rescaledKernel ρ r) w)
          (fun h => hy (hsupport r hr hrε w (ball_subset_closedBall hwball) h))
      simp only [he, zero_mul]
  have hderiv (i : Fin n) {y : Spacetime n} (hy : y ∈ tsupport χ) :
      spatialDeriv i (mollifiedValue u' ρ r) y =
        spatialDeriv i (mollifiedValue u ρ r) y :=
    congrArg (fun A : Spacetime n →L[ℝ] ℝ => A (spatialDirection i))
      (hconv.eventuallyEq_of_mem (isOpen_ball.mem_nhds (hχball hy))).fderiv_eq
  calc
    (∫ y, ∑ i, (χ y * spatialDeriv i (mollifiedValue u ρ r) y) ^ 2) =
        (∫ y, ∑ i, (χ y * spatialDeriv i (mollifiedValue u' ρ r) y) ^ 2) := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ tsupport χ
      · simp_rw [hderiv _ hy]
      · simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    _ ≤ B := henergy r hr
      (fun y hy => hsupport r hr hrε y (ball_subset_closedBall (hχball hy)))

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
