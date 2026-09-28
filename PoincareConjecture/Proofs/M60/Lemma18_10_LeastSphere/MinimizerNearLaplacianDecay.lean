import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSourceComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)





theorem suNearLaplacian_hessian_decay :
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
      ∀ a ∈ Metric.closedBall (0 : Plane) 1, ∀ r ∈ Ioc (0 : ℝ) 1,
        suHessianEnergy H (Metric.ball a r) ≤
          C * (suHessianEnergy H (Metric.ball 0 2) +
            Real.sqrt (∫ x in Metric.ball 0 2, ‖f x‖ ^ 4)) * Real.sqrt r := by
  obtain ⟨A, B, hA, hB, hcompare⟩ := suWeakHessian_disk_comparison
  obtain ⟨q, δ, hq, hq4, hδ, hsmall⟩ :=
    suComparison_smallness hA.le (show 0 ≤ 2 * B by positivity)
  let C := (1 + 4 * B * Real.sqrt Real.pi / q) / q
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro m u p H f hu hp hw hH hwH hf hres a ha r hr
  let I := Real.sqrt (∫ x in Metric.ball (0 : Plane) 2, ‖f x‖ ^ 4)
  let F := 2 * B * Real.sqrt Real.pi * I
  let E : ℝ → ℝ := fun t => suHessianEnergy H (Metric.ball a t)
  have hI : 0 ≤ I := Real.sqrt_nonneg _
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hsub {t : ℝ} (ht : t ≤ 1) : Metric.ball a t ⊆ Metric.ball (0 : Plane) 2 := by
    intro x hx
    have hx' := Metric.mem_ball.mp hx
    have ha' := Metric.mem_closedBall.mp ha
    have hd := dist_triangle x a (0 : Plane)
    exact Metric.mem_ball.mpr (by linarith)
  have hnonneg (t : ℝ) : 0 ≤ E t := integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hmono : MonotoneOn E (Ioc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact suHessianEnergy_mono (Metric.ball_subset_ball hst)
      (fun i j => (hH i j).mono_measure (Measure.restrict_mono (hsub ht.2) le_rfl))
  have hstep (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      E (q ^ 2 * t) ≤ q / 2 * E t + F * t := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball a t)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        (measure_ball_lt_top : volume (Metric.ball a t) < ⊤)⟩
    have hμ := Measure.restrict_mono (hsub ht.2) (le_rfl (a := volume))
    have hu' := hu.mono_measure hμ
    have hp' (i) := (hp i).mono_measure hμ
    have hH' (i j) := (hH i j).mono_measure hμ
    have hf' := hf.mono_measure hμ
    have hf2 : MemLp f 2 (volume.restrict (Metric.ball a t)) :=
      hf'.mono_exponent (by norm_num)
    have htr := suHessianTrace_le_residual hH' hf2 hδ.le
      (hres.filter_mono (ae_mono hμ))
    have hforce := suL4_source_disk_bound hf a ht.1 (hsub ht.2)
    have hqt : q ^ 2 * t ≤ t / 4 := by
      have hq2 : q ^ 2 ≤ 1 / 4 := by nlinarith
      calc
        _ ≤ 1 / 4 * t := mul_le_mul_of_nonneg_right hq2 ht.1.le
        _ = _ := by ring
    have hb := hcompare m a ht.1 hu' hp'
      (fun i b => (hw i b).restrict Metric.isOpen_ball (hsub ht.2)) hH'
      (fun i j b => (hwH i j b).restrict Metric.isOpen_ball (hsub ht.2))
      (q ^ 2 * t) (mul_pos (sq_pos_of_pos hq) ht.1) hqt
    rw [mul_div_cancel_right₀ _ ht.1.ne'] at hb
    have hcoeff := hsmall δ hδ.le le_rfl
    calc
      E (q ^ 2 * t) ≤ A * (q ^ 2) ^ 2 * E t +
          B * ∫ x in Metric.ball a t, ‖∑ i : Fin 2, H i i x‖ ^ 2 := hb
      _ ≤ A * (q ^ 2) ^ 2 * E t +
          B * (2 * δ ^ 2 * E t + 2 * ∫ x in Metric.ball a t, ‖f x‖ ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left htr hB)
      _ ≤ A * (q ^ 2) ^ 2 * E t +
          B * (2 * δ ^ 2 * E t + 2 * (Real.sqrt Real.pi * t * I)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hforce (by norm_num))) hB)
      _ = (A * (q ^ 2) ^ 2 + (2 * B) * δ ^ 2) * E t + F * t := by
        dsimp only [F]
        ring
      _ ≤ q / 2 * E t + F * t :=
        add_le_add (mul_le_mul_of_nonneg_right hcoeff (hnonneg t)) le_rfl
  have hdec := suEnergy_sqrt_decay hq (by linarith : q < 1) hF
    (hnonneg 1) hmono hstep r hr
  have hE1 : E 1 ≤ suHessianEnergy H (Metric.ball 0 2) :=
    suHessianEnergy_mono (hsub le_rfl) hH
  have hEtot : 0 ≤ suHessianEnergy H (Metric.ball (0 : Plane) 2) :=
    integral_nonneg fun x =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hconstant : (E 1 + 2 * F / q) / q ≤
      C * (suHessianEnergy H (Metric.ball 0 2) + I) := by
    dsimp only [C, F]
    apply (div_le_iff₀ hq).mpr
    rw [mul_right_comm ((1 + 4 * B * Real.sqrt Real.pi / q) / q),
      div_mul_cancel₀ _ hq.ne']
    have hcross : 0 ≤ (4 * B * Real.sqrt Real.pi / q) *
        suHessianEnergy H (Metric.ball 0 2) := by positivity
    rw [show 2 * (2 * B * Real.sqrt Real.pi * I) / q =
      (4 * B * Real.sqrt Real.pi / q) * I by ring]
    nlinarith
  exact hdec.trans (mul_le_mul_of_nonneg_right hconstant (Real.sqrt_nonneg r))

end PoincareConjecture.M60

end
