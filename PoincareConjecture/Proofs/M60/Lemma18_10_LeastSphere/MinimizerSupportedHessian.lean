import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem scalar_supported_hessian :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : Plane → ℝ}
      {p : Fin 2 → Plane → ℝ} {H : Fin 2 → Fin 2 → Plane → ℝ},
      MemLp u 2 volume → (∀ i, MemLp (p i) 2 volume) →
      (∀ i, HasWeakPartialDeriv i (p i) u univ) →
      (∀ i j, MemLp (H i j) 2 volume) →
      (∀ i j, HasWeakPartialDeriv j (H i j) (p i) univ) →
      (∀ i j x, x ∉ Metric.ball (0 : Plane) (3 / 2) → H i j x = 0) →
      suHessianEnergy H univ ≤ C *
        ((∫ x, ∑ i : Fin 2, p i x ^ 2) + (∫ x, u x ^ 2) +
          ∫ x, (∑ i : Fin 2, H i i x) ^ 2) := by
  have hclos2 : closure (Metric.ball (0 : Plane) 2) = Metric.closedBall 0 2 :=
    closure_ball _ (by norm_num)
  have hclos3 : closure (Metric.ball (0 : Plane) (3 / 2)) =
      Metric.closedBall 0 (3 / 2) := closure_ball _ (by norm_num)
  obtain ⟨C, hC, hb⟩ := suWeak_hessian_integral_le suPlaneLaplaceForm
    Metric.isOpen_ball (hclos2 ▸ isCompact_closedBall _ _) (subset_univ _)
    Metric.isOpen_ball (hclos3 ▸ isCompact_closedBall _ _)
    (by rw [hclos3]; exact Metric.closedBall_subset_ball (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro u p H hu hp hw hH hwH hz
  let f : Plane → ℝ := fun x => -(∑ i : Fin 2, H i i x)
  have hf : MemLp f 2 volume := (memLp_finsetSum _ (fun i _ => hH i i)).neg
  have hflux (j : Fin 2) : MemLp
      (fun x => ∑ i : Fin 2, suPlaneLaplaceForm.a x i j * p i x) 2 volume := by
    simpa [suPlaneLaplaceForm, Matrix.one_apply] using hp j
  have heq := suWeakEquation_of_hessian
    (fun i => (hp i).restrict (Metric.ball (0 : Plane) 2))
    (fun i => (hH i i).restrict (Metric.ball (0 : Plane) 2))
    (fun i => (hwH i i).restrict Metric.isOpen_ball (subset_univ _))
  obtain ⟨K, hKm, hKw, hKb⟩ := hb hu hf hp hw hflux (by
    intro φ hφ hc hs
    simpa [suPlaneLaplaceForm, Matrix.one_apply, f,
      Poincare.Analysis.Elliptic.Iteration.partialDeriv] using heq φ hφ hc hs)
  have hae (i j : Fin 2) : K i j =ᵐ[volume.restrict
      (Metric.ball (0 : Plane) (3 / 2))] H i j :=
    HasWeakPartialDeriv.ae_eq Metric.isOpen_ball (hKw i j)
      ((hwH i j).restrict Metric.isOpen_ball (subset_univ _))
      ((hKm i j).locallyIntegrable (by norm_num))
      (((hH i j).restrict _).locallyIntegrable (by norm_num))
  have hident : (∫ x in Metric.ball (0 : Plane) (3 / 2),
      ∑ j : Fin 2, ∑ i : Fin 2, K i j x ^ 2) = suHessianEnergy H univ := by
    calc
      _ = ∫ x in Metric.ball (0 : Plane) (3 / 2),
          ∑ j : Fin 2, ∑ i : Fin 2, H i j x ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hae i j]
          with x hx
        simp only [hx]
      _ = ∫ x, ∑ j : Fin 2, ∑ i : Fin 2, H i j x ^ 2 :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => by simp [hz _ _ x hx])
      _ = _ := by
        simp only [suHessianEnergy, Measure.restrict_univ, Real.norm_eq_abs, sq_abs]
        exact integral_congr_ae (Eventually.of_forall fun x => Finset.sum_comm)
  rw [hident] at hKb
  have hpint := integrable_finsetSum Finset.univ fun i _ => (hp i).integrable_sq
  have hfint : Integrable (fun x => (∑ i : Fin 2, H i i x) ^ 2) volume :=
    (memLp_finsetSum _ (fun i _ => hH i i)).integrable_sq
  have hpmono : (∫ x in Metric.ball (0 : Plane) 2, ∑ i : Fin 2, p i x ^ 2) ≤
      ∫ x, ∑ i : Fin 2, p i x ^ 2 :=
    setIntegral_le_integral hpint (Eventually.of_forall fun x =>
      Finset.sum_nonneg fun i _ => sq_nonneg (p i x))
  have humono : (∫ x in Metric.ball (0 : Plane) 2, u x ^ 2) ≤ ∫ x, u x ^ 2 :=
    setIntegral_le_integral hu.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg (u x))
  have hfmono : (∫ x in Metric.ball (0 : Plane) 2, (∑ i : Fin 2, H i i x) ^ 2) ≤
      ∫ x, (∑ i : Fin 2, H i i x) ^ 2 := setIntegral_le_integral hfint
    (Eventually.of_forall fun x => sq_nonneg (∑ i : Fin 2, H i i x))
  simp only [f, neg_sq] at hKb
  exact hKb.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hpmono humono) hfmono) hC)

theorem suL2_component_integrals {m : ℕ} {μ : Measure Plane}
    {u : Plane → EuclideanSpace ℝ (Fin m)} (hu : MemLp u 2 μ) :
    (∑ b : Fin m, ∫ x, (u x b) ^ 2 ∂μ) = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hc (b : Fin m) : MemLp (fun x => u x b) 2 μ :=
    (EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' hu
  rw [← integral_finsetSum _ (fun b _ => (hc b).integrable_sq)]
  exact integral_congr_ae (Eventually.of_forall fun x =>
    (EuclideanSpace.real_norm_sq_eq (u x)).symm)

theorem suSupported_weak_hessian_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ)
      {u : Plane → EuclideanSpace ℝ (Fin m)}
      {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
      {H : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m)},
      MemLp u 2 volume → (∀ i, MemLp (p i) 2 volume) →
      (∀ i b, HasWeakPartialDeriv i (fun x => p i x b) (fun x => u x b) univ) →
      (∀ i j, MemLp (H i j) 2 volume) →
      (∀ i j b, HasWeakPartialDeriv j (fun x => H i j x b) (fun x => p i x b) univ) →
      (∀ i j x, x ∉ Metric.ball (0 : Plane) (3 / 2) → H i j x = 0) →
      suHessianEnergy H univ ≤ C *
        ((∫ x, ∑ i : Fin 2, ‖p i x‖ ^ 2) + (∫ x, ‖u x‖ ^ 2) +
          ∫ x, ‖∑ i : Fin 2, H i i x‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := scalar_supported_hessian
  refine ⟨C, hC, ?_⟩
  intro m u p H hu hp hw hH hwH hz
  have hc {v : Plane → EuclideanSpace ℝ (Fin m)} (hv : MemLp v 2 volume) (b : Fin m) :
      MemLp (fun x => v x b) 2 volume := (EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' hv
  have hbound (b : Fin m) := hb (hc hu b) (fun i => hc (hp i) b) (fun i => hw i b)
    (fun i j => hc (hH i j) b) (fun i j => hwH i j b)
    (fun i j x hx => by rw [hz i j x hx]; rfl)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun b _ => hbound b
  rw [← suHessianEnergy_components
    (fun i j => by simpa only [Measure.restrict_univ] using hH i j)] at hsum
  have hpint (b : Fin m) (i : Fin 2) : Integrable (fun x => (p i x b) ^ 2) volume :=
    ((EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' (hp i)).integrable_sq
  have hgrad : (∑ b : Fin m, ∫ x, ∑ i : Fin 2, (p i x b) ^ 2) =
      ∫ x, ∑ i : Fin 2, ‖p i x‖ ^ 2 := by
    simp_rw [integral_finsetSum _ (fun i _ => hpint _ i)]
    rw [Finset.sum_comm]
    simp_rw [suL2_component_integrals (hp _)]
    exact (integral_finsetSum _ (fun i _ => (hp i).norm.integrable_sq)).symm
  have htrace : (∑ b : Fin m, ∫ x, (∑ i : Fin 2, H i i x b) ^ 2) =
      ∫ x, ‖∑ i : Fin 2, H i i x‖ ^ 2 := by
    have hproj (x : Plane) (b : Fin m) :
        (∑ i : Fin 2, H i i x) b = ∑ i : Fin 2, H i i x b :=
      map_sum (EuclideanSpace.proj (𝕜 := ℝ) b) (fun i : Fin 2 => H i i x) Finset.univ
    simpa only [hproj] using
      suL2_component_integrals (memLp_finsetSum Finset.univ (fun i _ => hH i i))
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib, hgrad,
    suL2_component_integrals hu, htrace] using hsum

end PoincareConjecture.M60

end
