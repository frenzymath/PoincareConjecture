





import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.Compatible










open Set Filter Metric

noncomputable section

namespace Poincare.GromovHausdorff

universe u

namespace CompatiblePointedCompactSystem



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




theorem range_stageEmbedding_mono
    (S : CompatiblePointedCompactSystem.{u}) {n m : ℕ} (hnm : n ≤ m) :
    Set.range (S.stageEmbedding n) ⊆ Set.range (S.stageEmbedding m) := by
  induction hnm with
  | refl => exact Set.Subset.rfl
  | @step m hnm ih =>
      exact ih.trans (S.range_stageEmbedding_mono_succ m)





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

