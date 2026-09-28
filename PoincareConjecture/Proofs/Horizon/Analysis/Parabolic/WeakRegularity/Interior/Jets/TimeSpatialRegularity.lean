




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.TimeBootstrap
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.SpatialRegularity










open Set MeasureTheory Metric
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

theorem exists_local_time_spatial_weak_jets
    {n m k : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    (hEll : C.IsUniformlyEllipticOn U)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hw : WeakSolutionOn C u U) {z : Spacetime n} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧
      HasTimeSpatialL2Jet (ball z r) m k u := by
  obtain ⟨V, C', u', hV, hzV, hVU, hC', hpc, hbc, hcc, hu', huc,
    hpEq, hbEq, hcEq, huEq, hw'⟩ := exists_weak_compact_extension hU hC hu hw hz
  have hC'V : C'.IsSmoothOn V :=
    ⟨fun i j => (hC'.1 i j).mono (subset_univ V),
      fun i => (hC'.2.1 i).mono (subset_univ V), hC'.2.2.mono (subset_univ V)⟩
  have hEllV : C'.IsUniformlyEllipticOn V := by
    obtain ⟨κ, hκ, hell⟩ := hEll
    refine ⟨κ, hκ, ?_⟩
    intro y hy ξ
    simp_rw [hpEq _ _ hy]
    exact hell y (hVU hy) ξ
  let ρ : ContDiffBump (0 : Spacetime n) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  obtain ⟨r, hr, hrV, hjet, ε, B, hε, hB, henergy⟩ :=
    exists_local_mollified_spatial_energy_all_orders (k := k + 2 * m)
      hV hC'V hEllV hu'.continuousOn hw' hzV ρ.contDiff ρ.hasCompactSupport
  have hballV : ball z r ⊆ V := ball_subset_closedBall.trans hrV
  have hforce (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hφc : HasCompactSupport φ) (hφr : tsupport φ ⊆ ball z r) :
      (∫ y, u' y * C'.adjoint φ y) = 0 := hw'.2 φ hφ hφc (hφr.trans hballV)
  have htime : HasTimeSpatialL2Jet (ball z r) m k u' :=
    time_spatial_jet_of_spatial_jet_and_weak_equation
      isOpen_ball hC' hpc hbc hcc hjet hforce
  have hueq : u' =ᵐ[volume.restrict (ball z r)] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact huEq (hballV hy)
  exact ⟨r, hr, hrV.trans hVU, htime.congr_ae hueq⟩


end Poincare.Analysis.Parabolic.WeakRegularity.Interior
