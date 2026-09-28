import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCutoffBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem suNearLaplacian_cutoff_hessian_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (m : ℕ) (χ : Plane → ℝ) (N : ℝ),
      0 ≤ N → ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) →
      tsupport χ ⊆ Metric.ball (0 : Plane) (3 / 2) →
      (∀ x ∈ Metric.ball (0 : Plane) 1, χ x = 1) →
      (∀ i : Fin 2, ∀ x, ‖fderiv ℝ χ x (EuclideanSpace.single i 1)‖ ≤ N) →
      (∀ i j : Fin 2, ∀ x,
        ‖fderiv ℝ (fun y => fderiv ℝ χ y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)‖ ≤ N) →
      ∀ {u : Plane → EuclideanSpace ℝ (Fin m)}
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
      suHessianEnergy H (Metric.ball 0 1) ≤ C * (1 + N ^ 2) *
        ((∫ x in Metric.ball 0 2, ∑ i : Fin 2, ‖p i x‖ ^ 2) +
          (∫ x in Metric.ball 0 2, ‖u x‖ ^ 2) + ∫ x in Metric.ball 0 2, ‖f x‖ ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := suSupported_weak_hessian_bound
  let δ := 1 / (16 * (A + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    apply (div_le_one (by positivity : 0 < 16 * (A + 1))).mpr
    linarith
  have hsmall : 8 * A * δ ^ 2 ≤ 1 / 2 := by
    have he : 16 * (A + 1) * δ = 1 := by
      dsimp only [δ]
      exact mul_one_div_cancel (by positivity : 16 * (A + 1) ≠ 0)
    have he' := congrArg (fun t : ℝ => t * δ) he
    nlinarith [sq_nonneg δ]
  refine ⟨δ, 304 * (A + 1), hδ, by positivity, ?_⟩
  intro m χ N hN hχ hc hrange hs hone hd hdd u p H f hu hp hw hH hwH hf hres
  let O : Set Plane := Metric.ball 0 2
  have hO : MeasurableSet O := Metric.isOpen_ball.measurableSet
  have hsO : tsupport χ ⊆ O := hs.trans (Metric.ball_subset_ball (by norm_num))
  let u0 : Plane → EuclideanSpace ℝ (Fin m) := fun x => χ x • u x
  let p0 := suCutoffColumn χ u p
  let H0 := suCutoffHessian χ u p H
  obtain ⟨hu0, hp0, hw0, hH0, hwH0⟩ := suCutoff_weak_jet hu hp hw hH hwH hχ hc hsO
  have hzero (x : Plane) (hx : x ∉ O) : χ x = 0 ∧
      ∀ i : Fin 2, fderiv ℝ χ x (EuclideanSpace.single i 1) = 0 := by
    refine ⟨image_eq_zero_of_notMem_tsupport (fun h => hx (hsO h)), ?_⟩
    intro i
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ χ y (EuclideanSpace.single i 1))
      (fun h => hx (hsO (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h)))
  have hb := hbound m hu0 hp0 hw0 hH0 hwH0 (fun i j x hx =>
    suCutoffHessian_eq_zero χ u p H i j x (fun h => hx (hs h)))
  let P := ∫ x in O, ∑ i : Fin 2, ‖p i x‖ ^ 2
  let U := ∫ x in O, ‖u x‖ ^ 2
  let F := ∫ x in O, ‖f x‖ ^ 2
  let E := suHessianEnergy H0 univ
  have hP : 0 ≤ P := integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hU : 0 ≤ U := integral_nonneg fun x => sq_nonneg _
  have hF : 0 ≤ F := integral_nonneg fun x => sq_nonneg _
  have hE : 0 ≤ E := integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hPi : Integrable (fun x => ∑ i : Fin 2, ‖p i x‖ ^ 2) (volume.restrict O) :=
    integrable_finsetSum _ (fun i _ => (hp i).norm.integrable_sq)
  have hUi : Integrable (fun x => ‖u x‖ ^ 2) (volume.restrict O) := hu.norm.integrable_sq
  have hFi : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict O) := hf.norm.integrable_sq
  have hEi : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖H0 i j x‖ ^ 2) volume :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hH0 i j).norm.integrable_sq))
  have hnormχ (x : Plane) : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hrange x).1]
    exact (hrange x).2
  have hUb : (∫ x, ‖u0 x‖ ^ 2) ≤ U := by
    calc
      _ ≤ ∫ x, O.indicator (fun y => ‖u y‖ ^ 2) x := by
        apply integral_mono hu0.norm.integrable_sq ((integrable_indicator_iff hO).mpr hUi)
        intro x
        by_cases hx : x ∈ O
        · rw [indicator_of_mem hx]
          have h := mul_le_mul_of_nonneg_right (hnormχ x) (norm_nonneg (u x))
          have h' : ‖u0 x‖ ≤ ‖u x‖ := by simpa only [u0, norm_smul, one_mul] using h
          exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h'
        · simp [(hzero x hx).1, hx]
      _ = U := integral_indicator hO
  have hPb : (∫ x, ∑ i : Fin 2, ‖p0 i x‖ ^ 2) ≤ 2 * P + 4 * N ^ 2 * U := by
    have hint := (hPi.const_mul 2).add (hUi.const_mul (4 * N ^ 2))
    calc
      _ ≤ ∫ x, O.indicator (fun y =>
          2 * (∑ i : Fin 2, ‖p i y‖ ^ 2) + 4 * N ^ 2 * ‖u y‖ ^ 2) x := by
        apply integral_mono (integrable_finsetSum _ (fun i _ => (hp0 i).norm.integrable_sq))
          ((integrable_indicator_iff hO).mpr hint)
        intro x
        by_cases hx : x ∈ O
        · rw [indicator_of_mem hx]
          exact suCutoffColumn_square_bound χ u p hN x (hnormχ x) (fun i => hd i x)
        · simp [suCutoffColumn, (hzero x hx).1, (hzero x hx).2, hx]
      _ = _ := by
        rw [integral_indicator hO, integral_add (hPi.const_mul 2)
          (hUi.const_mul (4 * N ^ 2)), integral_const_mul, integral_const_mul]
  have hTi := (memLp_finsetSum Finset.univ (fun i _ => hH0 i i)).norm.integrable_sq
  have hTb : (∫ x, ‖∑ i : Fin 2, H0 i i x‖ ^ 2) ≤
      8 * δ ^ 2 * E + 144 * N ^ 2 * (P + U) + 4 * F := by
    let k : Plane → ℝ := fun x =>
      144 * N ^ 2 * ((∑ i : Fin 2, ‖p i x‖ ^ 2) + ‖u x‖ ^ 2) + 4 * ‖f x‖ ^ 2
    have hk : Integrable k (volume.restrict O) :=
      ((hPi.add hUi).const_mul (144 * N ^ 2)).add (hFi.const_mul 4)
    have hpoint : ∀ᵐ x ∂volume, ‖∑ i : Fin 2, H0 i i x‖ ^ 2 ≤
        8 * δ ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖H0 i j x‖ ^ 2) + O.indicator k x := by
      have hres' := (ae_restrict_iff' hO).mp hres
      filter_upwards [hres'] with x hx
      by_cases hxO : x ∈ O
      · rw [indicator_of_mem hxO]
        have h := suCutoff_trace_residual_bound (fun i j => H i j x)
          (fun i j => H0 i j x) (fun i j => suCutoffError χ u p i j x) (f x)
          (hrange x).1 (hrange x).2 hδ.le hδ1
          (fun i j => suCutoffHessian_eq_smul_add_error χ u p H i j x) (hx hxO)
        have hR := suCutoffError_square_bound χ u p hN x (fun i => hd i x)
          (fun i j => hdd i j x)
        dsimp only [k]
        nlinarith
      · have hz (i j : Fin 2) : H0 i j x = 0 :=
          suCutoffHessian_eq_zero χ u p H i j x (fun h => hxO (hsO h))
        simp [hz, hxO]
    have hi := integral_mono_ae hTi
      ((hEi.const_mul (8 * δ ^ 2)).add ((integrable_indicator_iff hO).mpr hk)) hpoint
    simp only [Pi.add_apply] at hi
    rw [integral_add (hEi.const_mul (8 * δ ^ 2))
      ((integrable_indicator_iff hO).mpr hk), integral_const_mul, integral_indicator hO] at hi
    have hkval : (∫ x in O, k x) = 144 * N ^ 2 * (P + U) + 4 * F := by
      have hPU : Integrable (fun x => (∑ i : Fin 2, ‖p i x‖ ^ 2) + ‖u x‖ ^ 2)
          (volume.restrict O) := hPi.add hUi
      dsimp only [k]
      rw [integral_add (hPU.const_mul (144 * N ^ 2)) (hFi.const_mul 4),
        integral_const_mul, integral_const_mul, integral_add hPi hUi]
    rw [hkval] at hi
    simpa only [E, suHessianEnergy, Measure.restrict_univ, add_assoc] using hi
  have hEbound : E ≤ 304 * (A + 1) * (1 + N ^ 2) * (P + U + F) := by
    have hb' : E ≤ A * (8 * δ ^ 2 * E +
        (2 + 144 * N ^ 2) * P + (1 + 148 * N ^ 2) * U + 4 * F) := by
      have h := hb.trans (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hPb hUb) hTb) hA)
      convert h using 1 <;> first | rfl | ring
    have hs := mul_le_mul_of_nonneg_right hsmall hE
    have hNP := mul_nonneg (sq_nonneg N) hP
    have hNU := mul_nonneg (sq_nonneg N) hU
    have hNF := mul_nonneg (sq_nonneg N) hF
    have hAP := mul_nonneg hA hP
    have hAU := mul_nonneg hA hU
    have hAF := mul_nonneg hA hF
    have hANP := mul_nonneg hA hNP
    have hANU := mul_nonneg hA hNU
    have hANF := mul_nonneg hA hNF
    nlinarith
  have hinner : suHessianEnergy H (Metric.ball (0 : Plane) 1) ≤ E := by
    have heq : suHessianEnergy H (Metric.ball (0 : Plane) 1) =
        suHessianEnergy H0 (Metric.ball 0 1) := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x hx
      simp only [H0, suCutoffHessian_eq_of_eq_one χ u p H Metric.isOpen_ball hone _ _ x hx]
    rw [heq]
    exact suHessianEnergy_mono (subset_univ _)
      (fun i j => by simpa only [Measure.restrict_univ] using hH0 i j)
  exact hinner.trans hEbound

end PoincareConjecture.M60

end
