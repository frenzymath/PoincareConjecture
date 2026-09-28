import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerInteriorHessian

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.NirenbergEuclidean

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem fixed_cutoff :
    ∃ (χ : Plane → ℝ) (N : ℝ), 0 ≤ N ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      tsupport χ ⊆ Metric.ball (0 : Plane) (3 / 2) ∧
      (∀ x ∈ Metric.ball (0 : Plane) 1, χ x = 1) ∧
      (∀ i : Fin 2, ∀ x, ‖fderiv ℝ χ x (EuclideanSpace.single i 1)‖ ≤ N) ∧
      ∀ i j : Fin 2, ∀ x,
        ‖fderiv ℝ (fun y => fderiv ℝ χ y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)‖ ≤ N := by
  obtain ⟨χ, hχ, hc, hr, hone, hs⟩ := SmoothEllipticBilinearForm.exists_cutoff
    (isCompact_closedBall (0 : Plane) 1) Metric.isOpen_ball
    (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 3 / 2))
  have hd (i : Fin 2) : ContDiff ℝ ∞
      (fun x => fderiv ℝ χ x (EuclideanSpace.single i 1)) :=
    hχ.fderiv_right (by simp) |>.clm_apply contDiff_const
  have hdc (i : Fin 2) := hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hex (i : Fin 2) := (hdc i).exists_bound_of_continuous (hd i).continuous
  choose A hA using hex
  have hex2 (i j : Fin 2) :=
    ((hdc i).fderiv_apply ℝ (EuclideanSpace.single j 1)).exists_bound_of_continuous
      (((hd i).continuous_fderiv (by simp)).clm_apply continuous_const)
  choose B hB using hex2
  let N := (∑ i : Fin 2, |A i|) + ∑ i : Fin 2, ∑ j : Fin 2, |B i j|
  have hsumA : 0 ≤ ∑ i : Fin 2, |A i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsumB : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, |B i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨χ, N, add_nonneg hsumA hsumB, hχ, hc, fun x => hr ⟨x, rfl⟩,
    hs, fun x hx => hone x (Metric.ball_subset_closedBall hx), ?_, ?_⟩
  · intro i x
    have hi := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => abs_nonneg (A j)) (Finset.mem_univ i)
    exact (hA i x).trans ((le_abs_self _).trans (hi.trans (le_add_of_nonneg_right hsumB)))
  · intro i j x
    have hj := Finset.single_le_sum (s := Finset.univ)
      (fun k _ => abs_nonneg (B i k)) (Finset.mem_univ j)
    have hi := Finset.single_le_sum (s := Finset.univ)
      (fun k _ => Finset.sum_nonneg (s := Finset.univ)
        fun l _ => abs_nonneg (B k l)) (Finset.mem_univ i)
    exact (hB i j x).trans ((le_abs_self _).trans
      ((hj.trans hi).trans (le_add_of_nonneg_left hsumA)))

theorem suNearLaplacian_inner_hessian_bound :
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
      MemLp f 2 (volume.restrict (Metric.ball 0 2)) →
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 2),
        ‖(∑ i : Fin 2, H i i x) - f x‖ ≤
          δ * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2)) →
      suHessianEnergy H (Metric.ball 0 1) ≤ C *
        ((∫ x in Metric.ball 0 2, ∑ i : Fin 2, ‖p i x‖ ^ 2) +
          (∫ x in Metric.ball 0 2, ‖u x‖ ^ 2) + ∫ x in Metric.ball 0 2, ‖f x‖ ^ 2) := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := suNearLaplacian_cutoff_hessian_bound
  obtain ⟨χ, N, hN, hχ, hc, hr, hs, hone, hd, hdd⟩ := fixed_cutoff
  refine ⟨δ, C * (1 + N ^ 2), hδ, by positivity, ?_⟩
  intro m u p H f hu hp hw hH hwH hf hres
  exact hb m χ N hN hχ hc hr hs hone hd hdd hu hp hw hH hwH hf hres

end PoincareConjecture.M60

end
