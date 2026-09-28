import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerHarmonicComparison
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerPoissonHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.Iteration

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

def suHessianEnergy {E : Type*} [NormedAddCommGroup E]
    (H : Fin 2 → Fin 2 → Plane → E) (S : Set Plane) : ℝ :=
  ∫ x in S, ∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2

theorem suHessianEnergy_mono {E : Type*} [NormedAddCommGroup E]
    {H : Fin 2 → Fin 2 → Plane → E} {S T : Set Plane} (hTS : T ⊆ S)
    (hH : ∀ i j, MemLp (H i j) 2 (volume.restrict S)) :
    suHessianEnergy H T ≤ suHessianEnergy H S := by
  apply integral_mono_measure (Measure.restrict_mono hTS le_rfl)
  · exact Eventually.of_forall fun x => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _
  · exact integrable_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => (hH i j).norm.integrable_sq))

theorem suHessianEnergy_add_le {E : Type*} [NormedAddCommGroup E]
    {H K : Fin 2 → Fin 2 → Plane → E} {S : Set Plane}
    (hH : ∀ i j, MemLp (H i j) 2 (volume.restrict S))
    (hK : ∀ i j, MemLp (K i j) 2 (volume.restrict S)) :
    suHessianEnergy (fun i j x => H i j x + K i j x) S ≤
      2 * suHessianEnergy H S + 2 * suHessianEnergy K S := by
  have hiH := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hH i j).norm.integrable_sq))
  have hiK := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hK i j).norm.integrable_sq))
  have hiHK := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => ((hH i j).add (hK i j)).norm.integrable_sq))
  have hpoint (x : Plane) :
      (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x + K i j x‖ ^ 2) ≤
        2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2) +
          2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖K i j x‖ ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hn := norm_add_le (H i j x) (K i j x)
    have hn0 := norm_nonneg (H i j x + K i j x)
    nlinarith [sq_nonneg (‖H i j x‖ - ‖K i j x‖)]
  have hi := integral_mono hiHK ((hiH.const_mul 2).add (hiK.const_mul 2)) hpoint
  simpa only [Pi.add_apply, suHessianEnergy, integral_add (hiH.const_mul 2) (hiK.const_mul 2),
    integral_const_mul] using hi

theorem suHessianEnergy_sub_le {E : Type*} [NormedAddCommGroup E]
    {H K : Fin 2 → Fin 2 → Plane → E} {S : Set Plane}
    (hH : ∀ i j, MemLp (H i j) 2 (volume.restrict S))
    (hK : ∀ i j, MemLp (K i j) 2 (volume.restrict S)) :
    suHessianEnergy (fun i j x => H i j x - K i j x) S ≤
      2 * suHessianEnergy H S + 2 * suHessianEnergy K S := by
  simpa only [sub_eq_add_neg, suHessianEnergy, Pi.neg_apply, norm_neg] using
    suHessianEnergy_add_le hH (fun i j => (hK i j).neg)

private theorem weakPartial_sub {O : Set Plane} {v w p q : Plane → ℝ} (i : Fin 2)
    (hv : MemLp v 2 (volume.restrict O)) (hw : MemLp w 2 (volume.restrict O))
    (hp : MemLp p 2 (volume.restrict O)) (hq : MemLp q 2 (volume.restrict O))
    (hvp : HasWeakPartialDeriv i p v O) (hwq : HasWeakPartialDeriv i q w O) :
    HasWeakPartialDeriv i (fun x => p x - q x) (fun x => v x - w x) O := by
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hDLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2
      (volume.restrict O) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).restrict O
  simp_rw [sub_mul]
  have hsubv := integral_sub (hv.integrable_mul hDLp) (hw.integrable_mul hDLp)
  have hsubp := integral_sub (hp.integrable_mul hφLp) (hq.integrable_mul hφLp)
  simp only [Pi.mul_apply] at hsubv hsubp
  rw [hsubv, hsubp, hvp φ hφ hc hs, hwq φ hφ hc hs]
  ring

theorem suWeakLaplacian_hessian_comparison :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧
      ∀ (F : Lp ℝ 2 (RiemannianMetric.euclideanMetric 2).volumeMeasure)
        {u : Plane → ℝ} {p : Fin 2 → Plane → ℝ} {H : Fin 2 → Fin 2 → Plane → ℝ},
      MemLp u 2 (volume.restrict (Metric.ball 0 1)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 1))) →
      (∀ i, HasWeakPartialDeriv i (p i) u (Metric.ball 0 1)) →
      (∀ i j, MemLp (H i j) 2 (volume.restrict (Metric.ball 0 (1 / 2)))) →
      (∀ i j, HasWeakPartialDeriv j (H i j) (p i) (Metric.ball 0 (1 / 2))) →
      WeakEquation (Metric.ball 0 1) p F →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
        suHessianEnergy H (Metric.ball 0 r) ≤
          A * r ^ 2 * suHessianEnergy H (Metric.ball 0 (1 / 2)) + B * ‖F‖ ^ 2 := by
  obtain ⟨CP, hCP, hpoisson⟩ := suPlane_poisson_hessian
  obtain ⟨CH, hCH, hharmonic⟩ := suWeakHarmonic_hessian_decay
  refine ⟨4 * CH, (CH + 2) * CP, by positivity, by positivity, ?_⟩
  intro F u p H hu hp hw hH hwH heq r hr hr1
  obtain ⟨w, q, K, hwm, hqm, hqw, hweq, hKm, hKw, hKb⟩ := hpoisson F
  have h12 : Metric.ball (0 : Plane) 1 ⊆ Metric.ball 0 2 :=
    Metric.ball_subset_ball (by norm_num)
  have hhalf : Metric.ball (0 : Plane) (1 / 2) ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball (by norm_num)
  have hrs : Metric.ball (0 : Plane) r ⊆ Metric.ball 0 (1 / 2) :=
    Metric.ball_subset_ball (by linarith)
  have hwm1 := hwm.restrict (Metric.ball (0 : Plane) 1)
  have hqm1 (i) := (hqm i).mono_measure (Measure.restrict_mono h12 le_rfl)
  have hqw1 (i) := (hqw i).restrict Metric.isOpen_ball h12
  let v : Plane → ℝ := fun x => u x - w x
  let P : Fin 2 → Plane → ℝ := fun i x => p i x - q i x
  let J : Fin 2 → Fin 2 → Plane → ℝ := fun i j x => H i j x - K i j x
  have hv : MemLp v 2 (volume.restrict (Metric.ball 0 1)) := hu.sub hwm1
  have hP (i) : MemLp (P i) 2 (volume.restrict (Metric.ball 0 1)) := (hp i).sub (hqm1 i)
  have hvP (i) : HasWeakPartialDeriv i (P i) v (Metric.ball 0 1) :=
    weakPartial_sub i hu hwm1 (hp i) (hqm1 i) (hw i) (hqw1 i)
  have hJ (i j) : MemLp (J i j) 2 (volume.restrict (Metric.ball 0 (1 / 2))) :=
    (hH i j).sub (hKm i j)
  have hPJ (i j) : HasWeakPartialDeriv j (J i j) (P i) (Metric.ball 0 (1 / 2)) :=
    weakPartial_sub j ((hp i).mono_measure (Measure.restrict_mono hhalf le_rfl))
      ((hqm1 i).mono_measure (Measure.restrict_mono hhalf le_rfl))
      (hH i j) (hKm i j) (hwH i j) (hKw i j)
  have hvEq : WeakEquation (Metric.ball 0 1) P (fun _ => 0) := by
    intro φ hφ hφc hφO
    have hpint := integrable_finsetSum Finset.univ (fun i _ =>
      integrable_mul_partial_test ((hp i).locallyIntegrable (by norm_num)) hφ hφc i)
    have hqint := integrable_finsetSum Finset.univ (fun i _ =>
      integrable_mul_partial_test ((hqm1 i).locallyIntegrable (by norm_num)) hφ hφc i)
    simp only [P, sub_mul, Finset.sum_sub_distrib]
    rw [integral_sub hpint hqint, heq φ hφ hφc hφO]
    change (∫ x in Metric.ball 0 1, F x * φ x) -
      (∫ x in Metric.ball 0 1, ∑ i : Fin 2, q i x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in Metric.ball 0 1, 0 * φ x
    rw [hweq φ hφ hφc hφO, sub_self]
    simp
  have hdecay := hharmonic hv hP hvP hJ hPJ hvEq r hr hr1
  have hdecay' : suHessianEnergy J (Metric.ball 0 r) ≤
      CH * r ^ 2 * suHessianEnergy J (Metric.ball 0 (1 / 2)) := by
    simpa only [suHessianEnergy, Real.norm_eq_abs, sq_abs] using hdecay
  have hKbound : suHessianEnergy K (Metric.ball 0 (1 / 2)) ≤ CP * ‖F‖ ^ 2 := by
    have hswap : (fun x => ∑ k : Fin 2, ∑ i : Fin 2, K i k x ^ 2) =
        fun x => ∑ i : Fin 2, ∑ k : Fin 2, K i k x ^ 2 :=
      funext fun _ => Finset.sum_comm
    rw [hswap] at hKb
    simpa only [suHessianEnergy, Real.norm_eq_abs, sq_abs] using hKb
  have hJbound := suHessianEnergy_sub_le hH hKm
  change suHessianEnergy J _ ≤ _ at hJbound
  have hHsum : (fun i j x => J i j x + K i j x) = H := by
    funext i j x
    exact sub_add_cancel _ _
  have hsum := suHessianEnergy_add_le
    (fun i j => (hJ i j).mono_measure (Measure.restrict_mono hrs le_rfl))
    (fun i j => (hKm i j).mono_measure (Measure.restrict_mono hrs le_rfl))
  rw [hHsum] at hsum
  have hKmono := suHessianEnergy_mono hrs hKm
  have hfactor : 4 * CH * r ^ 2 + 2 ≤ CH + 2 := by
    have hrr : 4 * r ^ 2 ≤ 1 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hrr hCH.le
    nlinarith
  have hKn0 : 0 ≤ suHessianEnergy K (Metric.ball 0 (1 / 2)) := by
    unfold suHessianEnergy
    positivity
  calc
    _ ≤ 2 * suHessianEnergy J (Metric.ball 0 r) + 2 * suHessianEnergy K (Metric.ball 0 r) := hsum
    _ ≤ 2 * (CH * r ^ 2 *
        (2 * suHessianEnergy H (Metric.ball 0 (1 / 2)) +
          2 * suHessianEnergy K (Metric.ball 0 (1 / 2)))) +
        2 * suHessianEnergy K (Metric.ball 0 (1 / 2)) := by
      gcongr
      exact hdecay'.trans (mul_le_mul_of_nonneg_left hJbound (by positivity))
    _ = 4 * CH * r ^ 2 * suHessianEnergy H (Metric.ball 0 (1 / 2)) +
        (4 * CH * r ^ 2 + 2) * suHessianEnergy K (Metric.ball 0 (1 / 2)) := by ring
    _ ≤ 4 * CH * r ^ 2 * suHessianEnergy H (Metric.ball 0 (1 / 2)) +
        (CH + 2) * (CP * ‖F‖ ^ 2) := by
      gcongr
    _ = _ := by ring

end PoincareConjecture.M60

end
