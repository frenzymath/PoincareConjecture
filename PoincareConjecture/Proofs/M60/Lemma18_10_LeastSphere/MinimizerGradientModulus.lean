import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerHessianBound
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerNearLaplacianHolder










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem weak_const_mul {O : Set Plane} {u p : Plane → ℝ} {i : Fin 2}
    (hw : HasWeakPartialDeriv i p u O) (c : ℝ) :
    HasWeakPartialDeriv i (fun x => c * p x) (fun x => c * u x) O := by
  intro φ hφ hc hs
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hw φ hφ hc hs, mul_neg]

private theorem disk_integral_le_const {g : Plane → ℝ}
    (hg : Integrable g (volume.restrict (Metric.ball 0 2))) {B : ℝ}
    (hb : ∀ x ∈ Metric.ball (0 : Plane) 2, g x ≤ B) :
    (∫ x in Metric.ball 0 2, g x) ≤ 4 * Real.pi * B := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Plane) 2)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball (0 : Plane) 2) < ⊤)⟩
  have hvol : volume.real (Metric.ball (0 : Plane) 2) = 4 * Real.pi := by
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.toReal_ofReal Real.pi_pos.le]
    norm_num
  calc
    _ ≤ ∫ _x in Metric.ball (0 : Plane) 2, B := by
      apply integral_mono_ae hg (integrable_const B)
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx using hb x hx
    _ = _ := by simp only [integral_const, smul_eq_mul, Measure.real,
      Measure.restrict_apply_univ] at hvol ⊢; rw [hvol]






theorem suNearLaplacian_gradient_modulus :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (m : ℕ) (D F : ℝ), 0 ≤ D → 0 ≤ F →
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
      MemLp f 4 (volume.restrict (Metric.ball 0 2)) →
      (∀ i, ContinuousOn (p i) (Metric.ball 0 2)) →
      (∀ x ∈ Metric.ball (0 : Plane) 2, ‖u x‖ ≤ D) →
      (∀ i, ∀ x ∈ Metric.ball (0 : Plane) 2, ‖p i x‖ ≤ D) →
      (∀ x ∈ Metric.ball (0 : Plane) 2, ‖f x‖ ≤ F) →
      (∀ x ∈ Metric.ball (0 : Plane) 2,
        ‖(∑ i : Fin 2, H i i x) - f x‖ ≤
          δ * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2)) →
      ∀ i, ∀ x ∈ Metric.closedBall (0 : Plane) (1 / 4),
        ∀ y ∈ Metric.closedBall (0 : Plane) (1 / 4),
        dist (p i x) (p i y) ≤ C * (D + F) * Real.sqrt (Real.sqrt (dist x y)) := by
  obtain ⟨δH, CH, hδH, hCH, hHessian⟩ := suNearLaplacian_inner_hessian_bound
  obtain ⟨δQ, CQ, hδQ, hCQ, hHolder⟩ := suNearLaplacian_weak_gradient_holder
  let K := 12 * Real.pi * CH + 2 * Real.sqrt Real.pi + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨min δH δQ, 4 * CQ * Real.sqrt K, lt_min hδH hδQ, by positivity, ?_⟩
  intro m D F hD hF u p H f hu hp hw hH hwH hf hc huB hpB hfB hres
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Plane) 2)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball (0 : Plane) 2) < ⊤)⟩
  have hf2 : MemLp f 2 (volume.restrict (Metric.ball 0 2)) := hf.mono_exponent (by norm_num)
  have hresH : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Plane) 2),
      ‖(∑ i : Fin 2, H i i x) - f x‖ ≤
        δH * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact (hres x hx).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  have hHb := hHessian m hu hp hw hH hwH hf2 hresH
  have hUb := disk_integral_le_const hu.norm.integrable_sq
    (fun x hx => (sq_le_sq₀ (norm_nonneg _) hD).mpr (huB x hx))
  have hPb := disk_integral_le_const
    (integrable_finsetSum Finset.univ (fun i _ => (hp i).norm.integrable_sq))
    (B := 2 * D ^ 2) (by
      intro x hx
      have h0 := (sq_le_sq₀ (norm_nonneg _) hD).mpr (hpB (0 : Fin 2) x hx)
      have h1 := (sq_le_sq₀ (norm_nonneg _) hD).mpr (hpB (1 : Fin 2) x hx)
      simp only [Fin.sum_univ_two]
      linarith)
  have hFb := disk_integral_le_const hf2.norm.integrable_sq
    (fun x hx => (sq_le_sq₀ (norm_nonneg _) hF).mpr (hfB x hx))
  have hHb' : suHessianEnergy H (Metric.ball (0 : Plane) 1) ≤
      CH * (12 * Real.pi * D ^ 2 + 4 * Real.pi * F ^ 2) := by
    have h := hHb.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hPb hUb) hFb) hCH.le)
    exact h.trans_eq (by ring)
  have hs : (0 : ℝ) < 1 / 2 := by norm_num
  let a : Plane → Plane := fun x => 0 + (1 / 2 : ℝ) • x
  let v : Plane → EuclideanSpace ℝ (Fin m) := fun x => u (a x)
  let P : Fin 2 → Plane → EuclideanSpace ℝ (Fin m) := fun i x => (1 / 2 : ℝ) • p i (a x)
  let J : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m) :=
    fun i j x => (1 / 2 : ℝ) ^ 2 • H i j (a x)
  let ff : Plane → EuclideanSpace ℝ (Fin m) := fun x => (1 / 2 : ℝ) ^ 2 • f (a x)
  have hpre : (fun x : Plane => 0 + (1 / 2 : ℝ) • x) ⁻¹' Metric.ball (0 : Plane) 1 =
      Metric.ball 0 2 := by
    simpa only [show (1 / 2 : ℝ) * 2 = 1 by norm_num] using suAffine_preimage_ball 0 hs 2
  have hsub : Metric.ball (0 : Plane) 1 ⊆ Metric.ball 0 2 := Metric.ball_subset_ball (by norm_num)
  have ha (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) 2) :
      a x ∈ Metric.ball (0 : Plane) 2 := by
    have hx' : x ∈ (fun z : Plane => 0 + (1 / 2 : ℝ) • z) ⁻¹' Metric.ball (0 : Plane) 1 := by
      rwa [hpre]
    exact hsub hx'
  have hv : MemLp v 2 (volume.restrict (Metric.ball 0 2)) := by
    simpa only [hpre] using suAffine_memLp
      (hu.mono_measure (Measure.restrict_mono hsub le_rfl)) 0 hs
  have hP (i) : MemLp (P i) 2 (volume.restrict (Metric.ball 0 2)) := by
    have h : MemLp (fun x => p i (a x)) 2 (volume.restrict (Metric.ball 0 2)) := by
      simpa only [hpre] using suAffine_memLp
        ((hp i).mono_measure (Measure.restrict_mono hsub le_rfl)) 0 hs
    exact h.const_smul (1 / 2 : ℝ)
  have hJ (i j) : MemLp (J i j) 2 (volume.restrict (Metric.ball 0 2)) := by
    have h : MemLp (fun x => H i j (a x)) 2 (volume.restrict (Metric.ball 0 2)) := by
      simpa only [hpre] using suAffine_memLp
        ((hH i j).mono_measure (Measure.restrict_mono hsub le_rfl)) 0 hs
    exact h.const_smul ((1 / 2 : ℝ) ^ 2)
  have hff : MemLp ff 4 (volume.restrict (Metric.ball 0 2)) := by
    have h : MemLp (fun x => f (a x)) 4 (volume.restrict (Metric.ball 0 2)) := by
      simpa only [hpre] using suAffine_memLp
        (hf.mono_measure (Measure.restrict_mono hsub le_rfl)) 0 hs
    exact h.const_smul ((1 / 2 : ℝ) ^ 2)
  have hwP (i b) : HasWeakPartialDeriv i (fun x => P i x b) (fun x => v x b)
      (Metric.ball 0 2) := by
    simpa only [P, v, Function.comp_apply, PiLp.smul_apply, smul_eq_mul, hpre] using
      suAffine_weakPartial ((hw i b).restrict Metric.isOpen_ball hsub) 0 hs
  have hwJ (i j b) : HasWeakPartialDeriv j (fun x => J i j x b) (fun x => P i x b)
      (Metric.ball 0 2) := by
    have h := weak_const_mul
      (suAffine_weakPartial ((hwH i j b).restrict Metric.isOpen_ball hsub) 0 hs) (1 / 2 : ℝ)
    change HasWeakPartialDeriv j
      (fun x => (1 / 2 : ℝ) * ((1 / 2 : ℝ) * H i j (a x) b))
      (fun x => (1 / 2 : ℝ) * p i (a x) b) _ at h
    simpa only [J, P, PiLp.smul_apply, smul_eq_mul, pow_two, mul_assoc, hpre] using h
  have hresJ : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Plane) 2),
      ‖(∑ i : Fin 2, J i i x) - ff x‖ ≤
        δQ * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖J i j x‖ ^ 2) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have h := (hres (a x) (ha x hx)).trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
    have he : (∑ i : Fin 2, ∑ j : Fin 2, ‖J i j x‖ ^ 2) =
        (1 / 16 : ℝ) * (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j (a x)‖ ^ 2) := by
      simp only [J, norm_smul, mul_pow, ← Finset.mul_sum]
      norm_num
    have ht : (∑ i : Fin 2, J i i x) - ff x = (1 / 4 : ℝ) •
        ((∑ i : Fin 2, H i i (a x)) - f (a x)) := by
      simp only [J, ff, ← Finset.smul_sum, ← smul_sub]
      norm_num
    rw [he, ht, norm_smul, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    norm_num at h ⊢
    nlinarith
  obtain ⟨Q, hQc, hQae, hQb⟩ := hHolder m hv hP hwP hJ hwJ hff hresJ
  have hJenergy : suHessianEnergy J (Metric.ball (0 : Plane) 2) =
      (1 / 4 : ℝ) * suHessianEnergy H (Metric.ball 0 1) := by
    simpa only [J, a, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num] using suHessianEnergy_rescale H 0 hs 2
  have hfFb (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) 2) : ‖ff x‖ ≤ F := by
    have h := hfB (a x) (ha x hx)
    dsimp only [ff]
    rw [norm_smul]
    norm_num
    nlinarith [norm_nonneg (f (a x))]
  have hf4b := disk_integral_le_const (hff.integrable_norm_pow (by norm_num))
    (fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hfFb x hx) 4)
  have hfroot : Real.sqrt (∫ x in Metric.ball (0 : Plane) 2, ‖ff x‖ ^ 4) ≤
      2 * Real.sqrt Real.pi * F ^ 2 := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity, ?_⟩
    exact hf4b.trans_eq (by simp only [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring)
  have hroot : Real.sqrt (suHessianEnergy J (Metric.ball (0 : Plane) 2) +
      Real.sqrt (∫ x in Metric.ball 0 2, ‖ff x‖ ^ 4)) ≤ Real.sqrt K * (D + F) := by
    have hEF : suHessianEnergy J (Metric.ball (0 : Plane) 2) ≤
        12 * Real.pi * CH * (D + F) ^ 2 := by
      rw [hJenergy]
      have h0 : 0 ≤ suHessianEnergy H (Metric.ball (0 : Plane) 1) := integral_nonneg fun x =>
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hcross := mul_nonneg (mul_nonneg Real.pi_pos.le hCH.le) (mul_nonneg hD hF)
      have hFpos := mul_nonneg (mul_nonneg Real.pi_pos.le hCH.le) (sq_nonneg F)
      nlinarith
    have hF2 : F ^ 2 ≤ (D + F) ^ 2 := by nlinarith
    have hforce := hfroot.trans (mul_le_mul_of_nonneg_left hF2 (by positivity))
    calc
      _ ≤ Real.sqrt (K * (D + F) ^ 2) := Real.sqrt_le_sqrt (by dsimp only [K]; nlinarith)
      _ = _ := by rw [Real.sqrt_mul hK.le, Real.sqrt_sq (add_nonneg hD hF)]
  have hPc (i : Fin 2) : ContinuousOn (P i) (Metric.closedBall (0 : Plane) (1 / 2)) := by
    apply ((hc i).comp (by fun_prop) ?_).const_smul (1 / 2 : ℝ)
    intro x hx
    apply ha x
    exact (Metric.closedBall_subset_ball (by norm_num)) hx
  have heq (i : Fin 2) : EqOn (Q i) (P i) (Metric.closedBall (0 : Plane) (1 / 2)) := by
    have ho := Measure.eqOn_open_of_ae_eq (hQae i) Metric.isOpen_ball
      ((hQc i).mono Metric.ball_subset_closedBall) ((hPc i).mono Metric.ball_subset_closedBall)
    exact ho.of_subset_closure (hQc i) (hPc i) Metric.ball_subset_closedBall
      (by rw [closure_ball _ (by norm_num)])
  intro i x hx y hy
  have hdouble (z : Plane) (hz : z ∈ Metric.closedBall (0 : Plane) (1 / 4)) :
      (2 : ℝ) • z ∈ Metric.closedBall (0 : Plane) (1 / 2) := by
    have h := Metric.mem_closedBall.mp hz
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul] at h ⊢
    norm_num
    linarith
  have hh := hQb i ((2 : ℝ) • x) (hdouble x hx) ((2 : ℝ) • y) (hdouble y hy)
  rw [heq i (hdouble x hx), heq i (hdouble y hy)] at hh
  have hPval (z : Plane) : P i ((2 : ℝ) • z) = (1 / 2 : ℝ) • p i z := by
    simp [P, a, smul_smul]
  have hdist : dist ((2 : ℝ) • x) ((2 : ℝ) • y) = 2 * dist x y := by
    simp only [dist_eq_norm, ← smul_sub, norm_smul]
    norm_num
  rw [hPval, hPval, hdist, dist_eq_norm, ← smul_sub, norm_smul] at hh
  norm_num at hh
  have hquarter : Real.sqrt (Real.sqrt (2 * dist x y)) ≤
      2 * Real.sqrt (Real.sqrt (dist x y)) := by
    calc
      _ ≤ Real.sqrt (Real.sqrt (16 * dist x y)) :=
        Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by nlinarith [show 0 ≤ dist x y from dist_nonneg]))
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
  have hprod := mul_le_mul
    (mul_le_mul_of_nonneg_left hroot hCQ.le) hquarter
    (Real.sqrt_nonneg _) (by positivity)
  norm_num at hprod
  change dist (p i x) (p i y) ≤ _
  rw [dist_eq_norm]
  nlinarith

end PoincareConjecture.M60

end
