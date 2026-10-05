/-
Adapted from AxelWorkspace, revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source: MorganTianLib/Topology/RadialCoverage.lean.
Apache-2.0; see references/analysis/axel-workspace/LICENSE.Apache-2.0.txt.
-/

import PoincareLib.Topology.MetricSpace.GromovHausdorff.Limit.Compatible

/-!
# natural-radius radial coverage

The compact-stage properness bridge is phrased for every real radius.  In
applications the available exhaustion often supplies the stronger-looking but
more concrete statement at natural radii.  This file records the Archimedean
cofinality step explicitly, leaving the geometric natural-radius coverage
hypothesis visible.
-/

open Set Filter Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Coverage of each natural-radius closed ball by its corresponding
compact stage implies the all-real-radius coverage needed for properness. -/
theorem properSpace_completedLimit_of_nat_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ n : ℕ,
      Metric.closedBall S.completedLimit.base (n : ℝ) ⊆
        Set.range (S.stageEmbedding n)) :
    ProperSpace S.completedLimit.carrier := by
  apply properSpace_completedLimit_of_radial_stage_coverage S
  intro R
  obtain ⟨n, hn⟩ := exists_nat_ge R
  exact ⟨n, (Metric.closedBall_subset_closedBall hn).trans (hcover n)⟩

/-! The natural-radius adapter is a special case of the following cofinal
radius form.  This is the form used when compact limits are indexed by a
radius sequence chosen during diagonal extraction. -/

/-- **Math.** Coverage of the closed ball of radius `r n` by stage `n`, for a
cofinal radius sequence, implies the all-real-radius coverage needed for
properness. -/
theorem properSpace_completedLimit_of_cofinal_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop)
    (hcover : ∀ n : ℕ,
      Metric.closedBall S.completedLimit.base (r n) ⊆
        Set.range (S.stageEmbedding n)) :
    ProperSpace S.completedLimit.carrier := by
  apply S.properSpace_completedLimit_of_radial_stage_coverage
  intro R
  have hev : ∀ᶠ n : ℕ in atTop, R ≤ r n :=
    (Filter.tendsto_atTop.1 hr) R
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hev
  exact ⟨n, (Metric.closedBall_subset_closedBall (hn n le_rfl)).trans
    (hcover n)⟩

/-- **Math.** Eventual coverage along a cofinal radius sequence still implies
properness: a sufficiently late stage simultaneously exceeds any prescribed
radius and lies in the eventual coverage tail. -/
theorem properSpace_completedLimit_of_eventually_cofinal_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop)
    (hcover : ∀ᶠ n : ℕ in atTop,
      Metric.closedBall S.completedLimit.base (r n) ⊆
        Set.range (S.stageEmbedding n)) :
    ProperSpace S.completedLimit.carrier := by
  apply S.properSpace_completedLimit_of_radial_stage_coverage
  intro R
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hcover
  have hev : ∀ᶠ n : ℕ in atTop, R ≤ r n :=
    (Filter.tendsto_atTop.1 hr) R
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  let n := max N M
  have hNn : N ≤ n := Nat.le_max_left _ _
  have hMn : M ≤ n := Nat.le_max_right _ _
  have hrad : R ≤ r n := hM n hMn
  exact ⟨n, (Metric.closedBall_subset_closedBall hrad).trans (hN n hNn)⟩

/-- **Math.** The image of an earlier compact stage is contained in every later
stage image.  This iterates the consecutive compatibility maps, and is useful
when a coverage statement is only known beyond a finite prefix. -/
theorem range_stageEmbedding_mono
    (S : CompatiblePointedCompactSystem.{u}) {n m : ℕ} (hnm : n ≤ m) :
    Set.range (S.stageEmbedding n) ⊆ Set.range (S.stageEmbedding m) := by
  induction hnm with
  | refl => exact Set.Subset.rfl
  | @step m hnm ih =>
      exact ih.trans (S.range_stageEmbedding_mono_succ m)

/-- **Math.** Eventual natural-radius coverage, together with nested stage
images, suffices for properness of the completed common ambient.  The finite
prefix of stages is irrelevant because a sufficiently large later stage
contains each prescribed bounded ball. -/
theorem properSpace_completedLimit_of_eventually_nat_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ᶠ n : ℕ in atTop,
      Metric.closedBall S.completedLimit.base (n : ℝ) ⊆
        Set.range (S.stageEmbedding n)) :
    ProperSpace S.completedLimit.carrier := by
  apply S.properSpace_completedLimit_of_radial_stage_coverage
  intro R
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcover
  obtain ⟨nR, hnR⟩ := exists_nat_ge R
  let n := max N nR
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hnr : nR ≤ n := Nat.le_max_right _ _
  have hcov := hN n hnN
  refine ⟨n, (Metric.closedBall_subset_closedBall ?_).trans hcov⟩
  exact le_trans hnR (by exact_mod_cast hnr)

/-! Radial coverage also gives an explicit pointwise stage witness. -/

/-- **Math.** If every basepoint-centered closed ball is covered by a compact
stage image, then the increasing stage images exhaust the completed limit. -/
theorem iUnion_range_stageEmbedding_eq_univ_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n)) :
    (⋃ n : ℕ, Set.range (S.stageEmbedding n)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := hcover (dist S.completedLimit.base x)
  refine mem_iUnion.2 ⟨n, ?_⟩
  apply hn
  rw [Metric.mem_closedBall]
  calc
    dist x S.completedLimit.base = dist S.completedLimit.base x := dist_comm _ _
    _ ≤ dist S.completedLimit.base x := le_rfl

end CompatiblePointedCompactSystem

end Poincare.GromovHausdorff

#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.properSpace_completedLimit_of_nat_stage_coverage
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.properSpace_completedLimit_of_cofinal_stage_coverage
#print axioms Poincare.GromovHausdorff.CompatiblePointedCompactSystem.properSpace_completedLimit_of_eventually_cofinal_stage_coverage
