import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Distance








noncomputable section
set_option autoImplicit false

open Set Filter Topology
open Poincare.GromovHausdorff

namespace Poincare.Alexandrov



theorem exists_approximating_maps_of_pointedGHConverges
    {X : ℕ → FiniteDiameterBasedMetricSpace} {Y : FiniteDiameterBasedMetricSpace}
    (h : PointedGHConverges X Y) :
    ∃ f : ∀ j, Y.carrier → (X j).carrier,
      ∀ x y, Tendsto (fun j => dist (f j x) (f j y)) atTop (𝓝 (dist x y)) := by
  classical
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose R hR using fun j => exists_pointedGHRealization_lt_add (X j) Y (hε j)
  choose f hf using fun j y =>
    exists_left_point_lt_of_pointedHausdorffDist_lt (R j) (hR j) y
  refine ⟨f, fun x y => ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hδ : Tendsto (fun j => pointedGHDistance (X j) Y + ε j) atTop (𝓝 0) := by
    simpa only [add_zero] using h.2.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
    (show Tendsto (fun j => 2 * (pointedGHDistance (X j) Y + ε j)) atTop (𝓝 0) by
      simpa using hδ.const_mul 2)
  rw [← (R j).left_isometry.dist_eq, ← (R j).right_isometry.dist_eq]
  exact (dist_dist_dist_le _ _ _ _).trans (by linarith [hf j x, hf j y])



theorem eventually_injective_of_tendsto_dist
    {ι : Type*} [Finite ι] {X : ℕ → Type*} [∀ j, MetricSpace (X j)]
    {Y : Type*} [MetricSpace Y] {q : ι → Y} {f : ∀ j, ι → X j}
    (hq : Function.Injective q)
    (hf : ∀ a b, Tendsto (fun j => dist (f j a) (f j b)) atTop (𝓝 (dist (q a) (q b)))) :
    ∀ᶠ j in atTop, Function.Injective (f j) := by
  have hpair (a b : ι) : ∀ᶠ j in atTop, f j a = f j b → a = b := by
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (fun _ _ => hab)
    · have hpos : 0 < dist (q a) (q b) := dist_pos.mpr (hq.ne hab)
      filter_upwards [(hf a b).eventually_const_lt hpos] with j hj heq
      simp [heq] at hj
  simpa only [Function.Injective, Filter.eventually_all] using
    (Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (hpair a))

end Poincare.Alexandrov
