import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerLaplacianComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.Iteration

local notation "Plane" => EuclideanSpace ℝ (Fin 2)



theorem suWeakEquation_of_hessian {O : Set Plane}
    {p : Fin 2 → Plane → ℝ} {H : Fin 2 → Fin 2 → Plane → ℝ}
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hH : ∀ i, MemLp (H i i) 2 (volume.restrict O))
    (hw : ∀ i, HasWeakPartialDeriv i (H i i) (p i) O) :
    WeakEquation O p (fun x => -(∑ i : Fin 2, H i i x)) := by
  intro φ hφ hφc hφO
  have hi (i) := integrable_mul_partial_test
    ((hp i).locallyIntegrable (by norm_num)) hφ hφc i
  have hj (i) := integrable_mul_test ((hH i).locallyIntegrable (by norm_num)) hφ hφc
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [neg_mul, Finset.sum_mul]
  rw [integral_neg, integral_finsetSum _ (fun i _ => hj i), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => hw i φ hφ hφc hφO




theorem suWeakHessian_unit_comparison :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧
      ∀ {u : Plane → ℝ} {p : Fin 2 → Plane → ℝ} {H : Fin 2 → Fin 2 → Plane → ℝ},
      MemLp u 2 (volume.restrict (Metric.ball 0 1)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 1))) →
      (∀ i, HasWeakPartialDeriv i (p i) u (Metric.ball 0 1)) →
      (∀ i j, MemLp (H i j) 2 (volume.restrict (Metric.ball 0 1))) →
      (∀ i j, HasWeakPartialDeriv j (H i j) (p i) (Metric.ball 0 1)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
        suHessianEnergy H (Metric.ball 0 r) ≤
          A * r ^ 2 * suHessianEnergy H (Metric.ball 0 1) +
            B * ∫ x in Metric.ball 0 1, (∑ i : Fin 2, H i i x) ^ 2 := by
  obtain ⟨A, B, hA, hB, hbound⟩ := suWeakLaplacian_hessian_comparison
  refine ⟨A, B, hA, hB, ?_⟩
  intro u p H hu hp hw hH hwH r hr hr1
  let O : Set Plane := Metric.ball 0 1
  let g : Plane → ℝ := fun x => -(∑ i : Fin 2, H i i x)
  let G : Plane → ℝ := O.indicator g
  have hg : MemLp g 2 (volume.restrict O) :=
    (memLp_finsetSum _ (fun i _ => hH i i)).neg
  have hG : MemLp G 2 volume :=
    (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet).mpr hg
  have hGmetric : MemLp G 2 (RiemannianMetric.euclideanMetric 2).volumeMeasure := by
    simpa only [RiemannianMetric.euclideanMetric_volumeMeasure] using hG
  let F : Lp ℝ 2 (RiemannianMetric.euclideanMetric 2).volumeMeasure := hGmetric.toLp G
  have hFG : (F : Plane → ℝ) =ᵐ[volume] G := by
    simpa only [RiemannianMetric.euclideanMetric_volumeMeasure] using hGmetric.coeFn_toLp
  have hF : (F : Plane → ℝ) =ᵐ[volume.restrict O] g := by
    filter_upwards [hFG.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxO
    exact hx.trans (indicator_of_mem hxO g)
  have heq : WeakEquation O p F := by
    intro φ hφ hφc hφO
    rw [suWeakEquation_of_hessian hp (fun i => hH i i) (fun i => hwH i i) φ hφ hφc hφO]
    apply integral_congr_ae
    filter_upwards [hF] with x hx using congrArg (fun t => t * φ x) hx.symm
  have hnorm : ‖F‖ ^ 2 = ∫ x in O, (∑ i : Fin 2, H i i x) ^ 2 := by
    change ‖hGmetric.toLp G‖ ^ 2 = _
    rw [Lp.norm_toLp, eLpNorm_toReal_sq_eq_integral hGmetric,
      RiemannianMetric.euclideanMetric_volumeMeasure]
    have hind : (fun x => G x ^ 2) = O.indicator (fun x => g x ^ 2) := by
      ext x
      by_cases hx : x ∈ O <;> simp [G, hx]
    rw [hind, integral_indicator Metric.isOpen_ball.measurableSet]
    simp only [g, neg_sq]
    rfl
  have hhalf : Metric.ball (0 : Plane) (1 / 2) ⊆ O := Metric.ball_subset_ball (by norm_num)
  have h := hbound F hu hp hw
    (fun i j => (hH i j).mono_measure (Measure.restrict_mono hhalf le_rfl))
    (fun i j => (hwH i j).restrict Metric.isOpen_ball hhalf) heq r hr hr1
  rw [hnorm] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left
    (suHessianEnergy_mono hhalf hH) (show 0 ≤ A * r ^ 2 by positivity)) le_rfl)




theorem suHessianEnergy_components {m : ℕ} {S : Set Plane}
    {H : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hH : ∀ i j, MemLp (H i j) 2 (volume.restrict S)) :
    suHessianEnergy H S =
      ∑ a : Fin m, suHessianEnergy (fun i j x => H i j x a) S := by
  have hcomp (a : Fin m) (i j : Fin 2) :
      MemLp (fun x => H i j x a) 2 (volume.restrict S) :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' (hH i j)
  have hint (a : Fin m) := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hcomp a i j).integrable_sq))
  simp only [suHessianEnergy, Real.norm_eq_abs, sq_abs]
  rw [← integral_finsetSum _ (fun a _ => hint a)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [EuclideanSpace.real_norm_sq_eq]
  calc
    _ = ∑ i : Fin 2, ∑ a : Fin m, ∑ j : Fin 2, H i j x a ^ 2 :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm




theorem suWeakHessian_vector_unit_comparison :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ (m : ℕ)
      {u : Plane → EuclideanSpace ℝ (Fin m)}
      {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
      {H : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m)},
      MemLp u 2 (volume.restrict (Metric.ball 0 1)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 1))) →
      (∀ i a, HasWeakPartialDeriv i (fun x => p i x a) (fun x => u x a) (Metric.ball 0 1)) →
      (∀ i j, MemLp (H i j) 2 (volume.restrict (Metric.ball 0 1))) →
      (∀ i j a, HasWeakPartialDeriv j (fun x => H i j x a) (fun x => p i x a)
        (Metric.ball 0 1)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
        suHessianEnergy H (Metric.ball 0 r) ≤
          A * r ^ 2 * suHessianEnergy H (Metric.ball 0 1) +
            B * ∫ x in Metric.ball 0 1, ‖∑ i : Fin 2, H i i x‖ ^ 2 := by
  obtain ⟨A, B, hA, hB, hbound⟩ := suWeakHessian_unit_comparison
  refine ⟨A, B, hA, hB, ?_⟩
  intro m u p H hu hp hw hH hwH r hr hr1
  have hcomp (a : Fin m) (i j : Fin 2) :
      MemLp (fun x => H i j x a) 2 (volume.restrict (Metric.ball 0 1)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' (hH i j)
  have hscalar (a : Fin m) := hbound ((EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' hu)
    (fun i => (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' (hp i))
    (fun i => hw i a) (hcomp a) (fun i j => hwH i j a) r hr hr1
  have hsub : Metric.ball (0 : Plane) r ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball (by linarith)
  have hsum (a : Fin m) : MemLp (fun x => ∑ i : Fin 2, H i i x a) 2
      (volume.restrict (Metric.ball 0 1)) := memLp_finsetSum _ (fun i _ => hcomp a i i)
  have hproj (x : Plane) (a : Fin m) :
      (∑ i : Fin 2, H i i x) a = ∑ i : Fin 2, H i i x a := by
    exact map_sum (EuclideanSpace.proj (𝕜 := ℝ) a) (fun i : Fin 2 => H i i x) Finset.univ
  have htrace : (∫ x in Metric.ball 0 1, ‖∑ i : Fin 2, H i i x‖ ^ 2) =
      ∑ a : Fin m, ∫ x in Metric.ball 0 1, (∑ i : Fin 2, H i i x a) ^ 2 := by
    simp_rw [EuclideanSpace.real_norm_sq_eq, hproj]
    exact integral_finsetSum _ (fun a _ => (hsum a).integrable_sq)
  rw [suHessianEnergy_components
      (fun i j => (hH i j).mono_measure (Measure.restrict_mono hsub le_rfl)),
    suHessianEnergy_components hH, htrace]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => hscalar a

end PoincareConjecture.M60

end
