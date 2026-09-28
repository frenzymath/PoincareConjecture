import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityRepresentative
import Mathlib.Analysis.SpecialFunctions.SmoothTransition











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture.M65Boundary

private theorem transition_derivative_bound :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ t, |deriv Real.smoothTransition t| ≤ B) ∧
      ∀ t, t ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition t = 0 := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  have hzero (t : ℝ) (ht : t ∉ Icc (0 : ℝ) 1) : deriv Real.smoothTransition t = 0 := by
    have ht' : t < 0 ∨ 1 < t := by
      by_cases h : t < 0
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge (fun hh => ht ⟨le_of_not_gt h, hh⟩))
    rcases ht' with h | h
    · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [gt_mem_nhds h] with x hx
        exact Real.smoothTransition.zero_of_nonpos hx.le
      rw [heq.deriv_eq, deriv_const]
    · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [lt_mem_nhds h] with x hx
        exact Real.smoothTransition.one_of_one_le hx.le
      rw [heq.deriv_eq, deriv_const]
  refine ⟨max B 0, le_max_right _ _, ?_, hzero⟩
  intro t
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hb : |deriv Real.smoothTransition t| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB t ht
    exact hb.trans (le_max_left _ _)
  · rw [hzero t ht, abs_zero]
    exact le_max_right _ _

private theorem zero_diameter_test_approximants
    (test : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport test) {R : ℝ}
    (hs : tsupport test ⊆ ball (0 : LoopPlane) R)
    (hzero : ∀ z : LoopPlane, z 1 = 0 → test z = 0) :
    ∃ (tests : ℕ → 𝓢(LoopPlane, ℝ)) (B V : ℝ), 0 ≤ B ∧ 0 ≤ V ∧
      (∀ n, HasCompactSupport (tests n) ∧
        tsupport (tests n) ⊆ ball (0 : LoopPlane) R ∩ {z | 0 < z 1}) ∧
      (∀ n z, ‖tests n z‖ ≤ V) ∧
      (∀ n z i, ‖fderiv ℝ (tests n) z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤ B) ∧
      ∀ z : LoopPlane, 0 < z 1 → ∀ᶠ n in atTop, (tests n : LoopPlane → ℝ) =ᶠ[𝓝 z] test := by
  obtain ⟨B, hB, hBD, hBDzero⟩ := transition_derivative_bound
  let L : NNReal := ⟨SchwartzMap.seminorm ℝ 0 1 test, apply_nonneg _ _⟩
  have hDL (z : LoopPlane) : ‖fderiv ℝ test z‖ ≤ (L : ℝ) := by
    change ‖fderiv ℝ test z‖ ≤ SchwartzMap.seminorm ℝ 0 1 test
    simpa only [norm_iteratedFDeriv_one] using test.norm_iteratedFDeriv_le_seminorm ℝ 1 z
  have hLip : LipschitzWith L test :=
    lipschitzWith_of_nnnorm_fderiv_le test.differentiable
      (fun z => NNReal.coe_le_coe.mp (hDL z))
  have hvalue (z : LoopPlane) : |test z| ≤ (L : ℝ) * |z 1| := by
    let y := z - z 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1
    have hy : y 1 = 0 := by simp [y, EuclideanSpace.basisFun_apply]
    have hd : dist z y = |z 1| := by
      rw [dist_eq_norm, show z - y = z 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 by
        dsimp only [y]; abel, norm_smul, Real.norm_eq_abs,
        (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one]
    simpa only [hzero y hy, dist_zero_right, Real.norm_eq_abs, hd] using hLip.dist_le_mul z y
  let k := fun n : ℕ => (n : ℝ) + 1
  let chi := fun n (z : LoopPlane) => Real.smoothTransition (k n * z 1 - 1)
  have hk (n : ℕ) : 0 < k n := by dsimp only [k]; positivity
  have hchi (n : ℕ) : ContDiff ℝ ∞ (chi n) := by
    exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff).sub
        contDiff_const)
  have hcompact (n : ℕ) : HasCompactSupport (fun z : LoopPlane => chi n z * test z) :=
    hc.mul_left
  let tests (n : ℕ) : 𝓢(LoopPlane, ℝ) :=
    (hcompact n).toSchwartzMap ((hchi n).mul (test.smooth (⊤ : ℕ∞)))
  have htests (n : ℕ) (z : LoopPlane) : tests n z = chi n z * test z := rfl
  have htestD (n : ℕ) (z : LoopPlane) (i : Fin 2) :
      fderiv ℝ (tests n) z (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        chi n z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) +
          deriv Real.smoothTransition (k n * z 1 - 1) * k n *
            (EuclideanSpace.basisFun (Fin 2) ℝ i) 1 * test z := by
    have hlin := ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
      (x := z)).const_mul (k n) |>.sub_const 1
    have hh := (Real.smoothTransition.contDiffAt (x := k n * z 1 - 1) (n := 1)).differentiableAt
      one_ne_zero |>.hasDerivAt
    have hD := hh.comp_hasFDerivAt z hlin
    have hp := hD.mul test.differentiableAt.hasFDerivAt
    change fderiv ℝ
      ((Real.smoothTransition ∘ fun w : LoopPlane => k n * w 1 - 1) *
        (test : LoopPlane → ℝ)) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) = _
    have heq := hp.fderiv
    simp only [EuclideanSpace.proj, PiLp.proj_apply] at heq
    rw [heq]
    simp only [add_apply, smul_apply, smul_eq_mul, PiLp.proj_apply, Function.comp_apply, chi]
    ring
  have hboundD (n : ℕ) (z : LoopPlane) (i : Fin 2) :
      ‖fderiv ℝ (tests n) z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤
        (L : ℝ) + 2 * B * L := by
    have hchiB : |chi n z| ≤ 1 := by
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have htB : |fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤ (L : ℝ) := by
      simpa only [Real.norm_eq_abs, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one,
        mul_one] using (ContinuousLinearMap.le_opNorm (fderiv ℝ test z)
          (EuclideanSpace.basisFun (Fin 2) ℝ i)).trans
          (mul_le_mul_of_nonneg_right (hDL z)
            (norm_nonneg (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    have hfirst : |chi n z * fderiv ℝ test z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤ (L : ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul hchiB htB (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hsecond : |deriv Real.smoothTransition (k n * z 1 - 1) * k n *
        (EuclideanSpace.basisFun (Fin 2) ℝ i) 1 * test z| ≤ 2 * B * L := by
      by_cases hz : k n * z 1 - 1 ∈ Icc (0 : ℝ) 1
      · have hzpos : 0 ≤ z 1 := by nlinarith [hz.1, hk n]
        have hscale : k n * |z 1| ≤ 2 := by rw [abs_of_nonneg hzpos]; linarith [hz.2]
        have hbasis : |(EuclideanSpace.basisFun (Fin 2) ℝ i) 1| ≤ 1 := by
          fin_cases i <;> norm_num [EuclideanSpace.basisFun_apply]
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (hk n)]
        calc
          _ ≤ (B * k n * 1) * ((L : ℝ) * |z 1|) :=
            mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (hBD _) (hk n).le)
              hbasis (abs_nonneg _) (mul_nonneg hB (hk n).le))
              (hvalue z) (abs_nonneg _) (by positivity)
          _ = (B * L) * (k n * |z 1|) := by ring
          _ ≤ (B * L) * 2 := mul_le_mul_of_nonneg_left hscale (by positivity)
          _ = _ := by ring
      · rw [hBDzero _ hz, zero_mul, zero_mul, zero_mul, abs_zero]
        positivity
    rw [htestD, Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  refine ⟨tests, (L : ℝ) + 2 * B * L, SchwartzMap.seminorm ℝ 0 0 test,
    by positivity, apply_nonneg _ _, ?_, ?_, hboundD, ?_⟩
  · intro n
    have hsup : tsupport (tests n) ⊆ tsupport test := by
      exact tsupport_mul_subset_right
    have hheight : tsupport (tests n) ⊆ {z : LoopPlane | 1 ≤ k n * z 1} := by
      apply closure_minimal
      · intro z hz
        by_contra h
        change ¬1 ≤ k n * z 1 at h
        have hh : k n * z 1 - 1 ≤ 0 := by linarith [not_le.mp h]
        apply hz
        rw [htests, show chi n z = 0 from Real.smoothTransition.zero_of_nonpos hh, zero_mul]
      · exact isClosed_le continuous_const
          (continuous_const.mul (EuclideanSpace.proj 1).continuous)
    refine ⟨hcompact n, ?_⟩
    intro z hz
    have hh : 1 ≤ k n * z 1 := hheight hz
    exact ⟨hs (hsup hz), by have := hk n; change 0 < z 1; nlinarith⟩
  · intro n z
    rw [htests, norm_mul]
    have hh : ‖chi n z‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans
      (by simpa only [one_mul] using test.norm_le_seminorm ℝ z)
  · intro z hz
    obtain ⟨n0, hn0⟩ := exists_nat_gt (2 / z 1)
    filter_upwards [eventually_ge_atTop n0] with n hn
    have hheight : 2 < k n * z 1 := by
      have hh := (div_lt_iff₀ hz).mp hn0
      have hnn : (n0 : ℝ) ≤ n := Nat.cast_le.mpr hn
      dsimp only [k]
      nlinarith
    have hnear : ∀ᶠ w in 𝓝 z, 2 < k n * w 1 :=
      (continuous_const.mul (EuclideanSpace.proj 1).continuous).continuousAt.eventually
        (Ioi_mem_nhds hheight)
    filter_upwards [hnear] with w hw
    rw [htests, show chi n w = 1 from
      Real.smoothTransition.one_of_one_le (by linarith), one_mul]






theorem halfDisk_equation_zero_diameter_test {R : ℝ}
    (D : Fin 2 → LoopPlane → ℝ) (f : LoopPlane → ℝ)
    (hD : ∀ i, IntegrableOn (D i) (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hf : IntegrableOn f (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (heq : ∀ test : 𝓢(LoopPlane, ℝ), HasCompactSupport test →
      tsupport test ⊆ ball (0 : LoopPlane) R ∩ {z | 0 < z 1} →
      (∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
        ∑ i : Fin 2, D i z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          -(∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, f z * test z))
    (test : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport test)
    (hs : tsupport test ⊆ ball (0 : LoopPlane) R)
    (hzero : ∀ z : LoopPlane, z 1 = 0 → test z = 0) :
    (∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      ∑ i : Fin 2, D i z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        -(∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, f z * test z) := by
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  have hU : MeasurableSet U := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  obtain ⟨tests, B, V, hB, hV, htests, hvalue, hder, htend⟩ :=
    zero_diameter_test_approximants test hc hs hzero
  have hleft : Tendsto (fun n => ∫ z in U, ∑ i : Fin 2,
      D i z * fderiv ℝ (tests n) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) atTop
      (𝓝 (∫ z in U, ∑ i : Fin 2,
        D i z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i))) := by
    apply tendsto_integral_of_dominated_convergence (fun z => ∑ i : Fin 2, ‖D i z‖ * B)
    · intro n
      apply Finset.aestronglyMeasurable_fun_sum
      intro i _
      exact (hD i).1.mul
        ((((tests n).smooth 1).continuous_fderiv one_ne_zero).clm_apply
          (continuous_const (y := EuclideanSpace.basisFun (Fin 2) ℝ i))).aestronglyMeasurable
    · exact integrable_finsetSum _ fun i _ => (hD i).norm.mul_const B
    · intro n
      exact ae_of_all _ fun z => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hder n z i) (norm_nonneg _))
    · filter_upwards [ae_restrict_mem hU] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [htend z hz.2] with n hn
      exact Finset.sum_congr rfl fun i _ => by rw [hn.fderiv_eq]
  have hright : Tendsto (fun n => ∫ z in U, f z * tests n z) atTop
      (𝓝 (∫ z in U, f z * test z)) := by
    apply tendsto_integral_of_dominated_convergence (fun z => ‖f z‖ * V)
    · intro n
      exact hf.1.mul (tests n).continuous.aestronglyMeasurable
    · exact hf.norm.mul_const V
    · intro n
      exact ae_of_all _ fun z => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hvalue n z) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem hU] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [htend z hz.2] with n hn
      rw [hn.self_of_nhds]
  exact tendsto_nhds_unique hleft
    (hright.neg.congr (fun n => (heq (tests n) (htests n).1 (htests n).2).symm))

end PoincareConjecture.M65Boundary
