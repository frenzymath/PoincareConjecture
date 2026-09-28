import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerNearLaplacianDecay
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerHolderRepresentative










set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)



theorem suHessianEnergy_entry_bound {E : Type*} [NormedAddCommGroup E]
    {H : Fin 2 → Fin 2 → Plane → E} {S : Set Plane}
    (hH : ∀ i j, MemLp (H i j) 2 (volume.restrict S)) (i j : Fin 2) :
    (∫ x in S, ‖H i j x‖ ^ 2) ≤ suHessianEnergy H S := by
  apply integral_mono ((hH i j).norm.integrable_sq)
    (integrable_finsetSum Finset.univ (fun k _ =>
      integrable_finsetSum Finset.univ (fun l _ => (hH k l).norm.integrable_sq)))
  intro x
  exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖H i k x‖)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ =>
      Finset.sum_nonneg fun l _ => sq_nonneg ‖H k l x‖) (Finset.mem_univ i))





theorem suNearLaplacian_weak_gradient_holder :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (m : ℕ)
      {u : Plane → EuclideanSpace ℝ (Fin m)}
      {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
      {H : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
      {f : Plane → EuclideanSpace ℝ (Fin m)},
      MemLp u 2 (volume.restrict (Metric.ball 0 2)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 2))) →
      (∀ i b, HasWeakPartialDeriv i (fun x => p i x b) (fun x => u x b)
        (Metric.ball 0 2)) →
      (∀ i j, MemLp (H i j) 2 (volume.restrict (Metric.ball 0 2))) →
      (∀ i j b, HasWeakPartialDeriv j (fun x => H i j x b) (fun x => p i x b)
        (Metric.ball 0 2)) →
      MemLp f 4 (volume.restrict (Metric.ball 0 2)) →
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 2),
        ‖(∑ i : Fin 2, H i i x) - f x‖ ≤
          δ * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2)) →
      ∃ P : Fin 2 → Plane → EuclideanSpace ℝ (Fin m),
        (∀ i, ContinuousOn (P i) (Metric.closedBall 0 (1 / 2))) ∧
        (∀ i, P i =ᵐ[volume.restrict (Metric.ball 0 (1 / 2))] p i) ∧
        ∀ i, ∀ x ∈ Metric.closedBall (0 : Plane) (1 / 2),
          ∀ y ∈ Metric.closedBall (0 : Plane) (1 / 2),
          dist (P i x) (P i y) ≤
            C * Real.sqrt (suHessianEnergy H (Metric.ball 0 2) +
              Real.sqrt (∫ z in Metric.ball 0 2, ‖f z‖ ^ 4)) *
                Real.sqrt (Real.sqrt (dist x y)) := by
  obtain ⟨δ, A, hδ, hA, hdecay⟩ := suNearLaplacian_hessian_decay
  let C := 640 * Real.sqrt Real.pi * Real.sqrt A / Real.pi
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro m u p H f hu hp hw hH hwH hf hres
  let K := A * (suHessianEnergy H (Metric.ball 0 2) +
    Real.sqrt (∫ z in Metric.ball 0 2, ‖f z‖ ^ 4))
  have hK : 0 ≤ K := by
    dsimp only [K, suHessianEnergy]
    exact mul_nonneg hA.le (add_nonneg
      (integral_nonneg fun x => Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg ‖H i j x‖) (Real.sqrt_nonneg _))
  have hg (i : Fin 2) := suWeakGradient_holder_representative (hp i) (hH i)
    (hwH i) hK (fun j a ha r hr =>
      (suHessianEnergy_entry_bound
        (fun k l => (hH k l).mono_measure (Measure.restrict_mono
          (show Metric.ball a r ⊆ Metric.ball (0 : Plane) 2 from by
            intro x hx
            have hx' := Metric.mem_ball.mp hx
            have ha' := Metric.mem_closedBall.mp ha
            have hd := dist_triangle x a (0 : Plane)
            exact Metric.mem_ball.mpr (by linarith [hr.2])) le_rfl)) i j).trans
        (hdecay m hu hp hw hH hwH hf hres a ha r hr))
  choose P hcont hae hholder using hg
  refine ⟨P, hcont, hae, ?_⟩
  intro i x hx y hy
  have hconstant : 640 * Real.sqrt Real.pi * Real.sqrt K / Real.pi =
      C * Real.sqrt (suHessianEnergy H (Metric.ball 0 2) +
        Real.sqrt (∫ z in Metric.ball 0 2, ‖f z‖ ^ 4)) := by
    dsimp only [K, C]
    rw [Real.sqrt_mul hA.le]
    ring
  simpa only [hconstant] using hholder i x hx y hy

end PoincareConjecture.M60

end
