import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.SmoothedCurrentPotential

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Manifold ContDiff Convolution ENNReal

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.DifferenceQuotient

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "b" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)

theorem observedWeakAnnulus_local_current_potential_approximation
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (R : E →L[ℝ] Plane) (hnorm : ∀ q, ‖R (e q)‖ = 1)
    {c0 c1 : ℝ → M} (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (center : Plane) {radius : ℝ} (hr : 0 < radius)
    (hball : Metric.closedBall center radius ⊆ S) :
    ∃ F : ℕ → Plane → ℝ, (∀ j, ContDiff ℝ ∞ (F j)) ∧ ∀ i : Fin 2,
      Tendsto (fun j => eLpNorm (fun p => fderiv ℝ (F j) p (b i) -
        planarCircleCurrent (R (e (A.map p))) (R (A.column i p))) 2
          (volume.restrict (Metric.ball center radius))) atTop (𝓝 0) := by
  classical
  obtain ⟨delta, hdelta, hpotential⟩ :=
    observedWeakAnnulus_smoothed_circle_current_potential e he R hnorm A center hr hball
  let eps := fun j : ℕ => min delta (1 / (j + 1 : ℝ))
  have heps (j : ℕ) : 0 < eps j := lt_min hdelta (by positivity)
  have hepsz : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps, min_eq_right hdelta.le] using
      (tendsto_const_nhds (x := delta)).min
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose F hF hDF using fun j => hpotential (eps j) (heps j) (min_le_left _ _)
  refine ⟨F, hF, ?_⟩
  intro i
  let J := fun p => planarCircleCurrent (R (e (A.map p))) (R (A.column i p))
  let U := (S).indicator J
  have hU : MemLp U 2 volume :=
    (memLp_indicator_iff_restrict isOpen_interior.measurableSet).mpr
      (observedWeakAnnulus_circle_current_memLp e R hnorm A i)
  have hlim := tendsto_eLpNorm_mollifyEps_sub heps hepsz
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hU
  have hbound (j : ℕ) :
      eLpNorm (fun p => fderiv ℝ (F j) p (b i) - J p) 2
        (volume.restrict (Metric.ball center radius)) ≤
      eLpNorm (fun p => mollifyEps (heps j) U p - U p) 2 volume := by
    calc
      _ = eLpNorm (fun p => mollifyEps (heps j) U p - U p) 2
          (volume.restrict (Metric.ball center radius)) := eLpNorm_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
        rw [hDF j p hp i]
        have hm := hball (Metric.ball_subset_closedBall hp)
        simp only [U, J, mollifyEps, indicator_of_mem hm])
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

end PoincareConjecture.M64
