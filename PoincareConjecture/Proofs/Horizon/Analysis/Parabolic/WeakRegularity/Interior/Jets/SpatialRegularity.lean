




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.SpatialBootstrap
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.SpatialJetMollification
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.GlobalSpatialJets









open Set MeasureTheory Filter Metric
open Poincare.Analysis.Convolution
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

theorem exists_local_mollified_spatial_energy_all_orders
    {n k : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    (hEll : C.IsUniformlyEllipticOn U)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hw : WeakSolutionOn C u U) {z : Spacetime n} (hz : z ∈ U)
    {ρ : Spacetime n → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) :
    ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ U ∧ HasSpatialL2Jet (ball z s) k u ∧
      ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
        (∫ y in ball z s, ∑ p : Fin k → Fin n,
          (iteratedSpatialDeriv k p (mollifiedValue u ρ r) y) ^ 2) ≤ B := by
  obtain ⟨V, C', u', hV, hzV, hVU, hC', hpc, hbc, hcc, hu', huc,
    hpEq, hbEq, hcEq, huEq, hw'⟩ := exists_weak_compact_extension hU hC hu hw hz
  obtain ⟨κ, hκ, hell⟩ := hEll
  have hEllV : C'.IsUniformlyEllipticOn V := by
    refine ⟨κ, hκ, ?_⟩
    intro y hy ξ
    simp_rw [hpEq _ _ hy]
    exact hell y (hVU hy) ξ
  have hC'V : C'.IsSmoothOn V :=
    ⟨fun i j => (hC'.1 i j).mono (subset_univ V),
      fun i => (hC'.2.1 i).mono (subset_univ V), hC'.2.2.mono (subset_univ V)⟩
  obtain ⟨R, hR, hRV, g, hgm, hgc, hweak⟩ :=
    exists_global_l2_spatial_weak_derivatives hV hC'V hEllV hu'.continuousOn hw' hzV
  have hballV : ball z R ⊆ V := ball_subset_closedBall.trans hRV
  have hwR : WeakSolutionOn C' u' (ball z R) :=
    WeakSolutionOn.restrict isOpen_ball hballV hw'
  have hu2 : MemLp u' 2 (volume.restrict (ball z R)) :=
    hu'.memLp_of_hasCompactSupport huc
  have hforce (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hφc : HasCompactSupport φ) (hφR : tsupport φ ⊆ ball z R) :
      (∫ y, u' y * C'.adjoint φ y) = ∫ y, φ y * (0 : ℝ) := by
    simpa only [mul_zero, integral_zero] using hwR.2 φ hφ hφc hφR
  have hEllz : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, C'.principal i j z * ξ i * ξ j := by
    intro ξ
    simp_rw [hpEq _ _ hzV]
    exact hell z hz ξ
  obtain ⟨t, ht, htR, hjet, hgjet⟩ := exists_local_forced_spatial_jet
    isOpen_ball hC' hpc hbc hcc hu2 (HasSpatialL2Jet.zero (ball z R) k)
    (fun i => (hgm i).restrict _) hforce hweak (mem_ball_self hR) hκ hEllz
  have htV : ball z t ⊆ V := ball_subset_closedBall.trans (htR.trans hballV)
  have hueq : u' =ᵐ[volume.restrict (ball z t)] u := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact huEq (htV hy)
  have hjetu : HasSpatialL2Jet (ball z t) k u :=
    (hjet.of_le (by omega : k ≤ k + 2)).congr_ae hueq
  obtain ⟨s, hs, hst, ε, B, hε, hB, henergy⟩ :=
    hjetu.exists_uniform_mollified_spatial_energy isOpen_ball (mem_ball_self ht) hρ hρc
  exact ⟨s, hs, hst.trans (htV.trans hVU),
    hjetu.restrict (ball_subset_closedBall.trans hst), ε, B, hε, hB, henergy⟩


end Poincare.Analysis.Parabolic.WeakRegularity.Interior
