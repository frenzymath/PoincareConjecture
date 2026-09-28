import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.LocalEnergy

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

private theorem directional_mul {f g : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (y w : Spacetime n) :
    fderiv ℝ (fun x => f x * g x) y w =
      fderiv ℝ f y w * g y + f y * fderiv ℝ g y w := by
  rw [fderiv_fun_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

private theorem second_mul {f g : Spacetime n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i j : Fin n) (y : Spacetime n) :
    spatialSecond i j (fun x => f x * g x) y =
      spatialSecond i j f y * g y + spatialDeriv j f y * spatialDeriv i g y +
        spatialDeriv i f y * spatialDeriv j g y + f y * spatialSecond i j g y := by
  have he : spatialDeriv j (fun x => f x * g x) =
      fun x => spatialDeriv j f x * g x + f x * spatialDeriv j g x := by
    funext x
    exact directional_mul hf hg x (spatialDirection j)
  dsimp only [spatialSecond]
  rw [he]
  change fderiv ℝ (fun x => spatialDeriv j f x * g x + f x * spatialDeriv j g x)
    y (spatialDirection i) = _
  rw [fderiv_fun_add
    (((contDiff_spatialDeriv hf j).mul hg).differentiable (by simp) y)
    ((hf.mul (contDiff_spatialDeriv hg j)).differentiable (by simp) y)]
  simp only [add_apply,
    directional_mul (contDiff_spatialDeriv hf j) hg,
    directional_mul hf (contDiff_spatialDeriv hg j)]
  simp only [spatialDeriv]
  ring

private theorem cutoff_residual {χ u : Spacetime n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (a : Fin n → Fin n → Spacetime n → ℝ) (y : Spacetime n) :
    timeDeriv (fun x => χ x * u x) y -
        ∑ i, ∑ j, a i j y * spatialSecond i j (fun x => χ x * u x) y =
      χ y * (timeDeriv u y - ∑ i, ∑ j, a i j y * spatialSecond i j u y) +
        (timeDeriv χ y - ∑ i, ∑ j, a i j y * spatialSecond i j χ y) * u y +
        ∑ i, (-(∑ j, (a i j y + a j i y) * spatialDeriv j χ y)) *
          spatialDeriv i u y := by
  have ht := directional_mul hχ hu y (0, 1)
  change timeDeriv (fun x => χ x * u x) y =
    timeDeriv χ y * u y + χ y * timeDeriv u y at ht
  rw [ht]
  simp_rw [second_mul hχ hu]
  simp only [mul_add, Finset.sum_add_distrib, mul_sub, sub_mul,
    Finset.mul_sum, Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
  have hcross : (∑ i, ∑ j, a i j y * (spatialDeriv i χ y * spatialDeriv j u y)) =
      ∑ i, ∑ j, a j i y * spatialDeriv j χ y * spatialDeriv i u y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hcross]
  ring_nf
  simp only [Finset.sum_add_distrib]
  ring

theorem exists_local_second_parabolic_energy
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {a : Fin n → Fin n → Spacetime n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j) U)
    {z : Spacetime n} (hz : z ∈ U) {κ : ℝ} (hκ : 0 < κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, a i j z * ξ i * ξ j) :
    ∃ r : ℝ, 0 < r ∧ closedBall z (2 * r) ⊆ U ∧
      ∃ B : ℝ, 0 < B ∧ ∀ u : Spacetime n → ℝ, ContDiff ℝ ∞ u →
        (∫ y in ball z r, (timeDeriv u y) ^ 2) + (κ ^ 2 / 2) *
            (∫ y in ball z r, ∑ i, ∑ j, (spatialSecond i j u y) ^ 2) ≤
          B * (∫ y in closedBall z (2 * r),
            (timeDeriv u y - ∑ i, ∑ j, a i j y * spatialSecond i j u y) ^ 2 +
              u y ^ 2 + ∑ i, (spatialDeriv i u y) ^ 2) := by
  obtain ⟨s, hs, hsU, hcoercive⟩ := exists_local_principal_parabolic_coercivity hU ha hz hκ hEll
  let χ : ContDiffBump z :=
    { rIn := s / 4
      rOut := s / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let K := closedBall z (s / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKU : K ⊆ U := (closedBall_subset_closedBall (by linarith : s / 2 ≤ s)).trans hsU
  have hχK : tsupport χ = K := χ.tsupport_eq
  have hχs : tsupport χ ⊆ ball z s := by
    rw [hχK]
    exact closedBall_subset_ball (by linarith)
  let q : Spacetime n → ℝ := fun y => timeDeriv χ y -
    ∑ i, ∑ j, a i j y * spatialSecond i j χ y
  let b : Fin n → Spacetime n → ℝ := fun i y =>
    -(∑ j, (a i j y + a j i y) * spatialDeriv j χ y)
  have hq : ContinuousOn q K := by
    apply (contDiff_timeDeriv χ.contDiff).continuous.continuousOn.sub
    exact continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      ((ha i j).continuousOn.mono hKU).mul (contDiff_spatialSecond χ.contDiff i j).continuous.continuousOn))
  have hb (i : Fin n) : ContinuousOn (b i) K := by
    apply ContinuousOn.neg
    exact continuousOn_finsetSum _ (fun j _ =>
      (((ha i j).continuousOn.mono hKU).add ((ha j i).continuousOn.mono hKU)).mul
        (contDiff_spatialDeriv χ.contDiff j).continuous.continuousOn)
  let C : Spacetime n → ℝ := fun y => χ y ^ 2 + q y ^ 2 + ∑ i, b i y ^ 2
  have hC : ContinuousOn C K :=
    ((χ.continuous.continuousOn.pow 2).add (hq.pow 2)).add
      (continuousOn_finsetSum _ (fun i _ => (hb i).pow 2))
  obtain ⟨M, hM⟩ := hK.bddAbove_image hC
  let L := max M 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCL (y : Spacetime n) (hy : y ∈ K) : C y ≤ L :=
    (hM ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  refine ⟨s / 4, by positivity, ?_, 6 * L, by positivity, ?_⟩
  · convert hKU using 1
    congr 1
    ring
  intro u hu
  let v : Spacetime n → ℝ := fun y => χ y * u y
  let P (w : Spacetime n → ℝ) : Spacetime n → ℝ := fun y =>
    timeDeriv w y - ∑ i, ∑ j, a i j y * spatialSecond i j w y
  let F : Spacetime n → ℝ := fun y => P u y ^ 2 + u y ^ 2 + ∑ i, spatialDeriv i u y ^ 2
  have hv : ContDiff ℝ ∞ v := χ.contDiff.mul hu
  have hvc : HasCompactSupport v := χ.hasCompactSupport.mul_right
  have hvs : tsupport v ⊆ tsupport χ := tsupport_mul_subset_left
  have hPv (y : Spacetime n) : P v y = χ y * P u y + q y * u y +
      ∑ i, b i y * spatialDeriv i u y := cutoff_residual χ.contDiff hu a y
  have hpoint (y : Spacetime n) (hy : y ∈ K) : P v y ^ 2 ≤ 3 * L * F y := by
    have hsum : 0 ≤ ∑ i, b i y ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hgrad : 0 ≤ ∑ i, spatialDeriv i u y ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hχL : χ y ^ 2 ≤ L := by have := hCL y hy; dsimp only [C] at this; nlinarith [sq_nonneg (q y)]
    have hqL : q y ^ 2 ≤ L := by have := hCL y hy; dsimp only [C] at this; nlinarith [sq_nonneg (χ y)]
    have hbL : (∑ i, b i y ^ 2) ≤ L := by have := hCL y hy; dsimp only [C] at this; nlinarith [sq_nonneg (χ y), sq_nonneg (q y)]
    have hχP := mul_le_mul_of_nonneg_right hχL (sq_nonneg (P u y))
    have hqu := mul_le_mul_of_nonneg_right hqL (sq_nonneg (u y))
    have hbg := (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => b i y)
      (fun i => spatialDeriv i u y)).trans (mul_le_mul_of_nonneg_right hbL hgrad)
    rw [hPv]
    dsimp only [F]
    nlinarith [sq_nonneg (χ y * P u y - q y * u y),
      sq_nonneg (χ y * P u y - ∑ i, b i y * spatialDeriv i u y),
      sq_nonneg (q y * u y - ∑ i, b i y * spatialDeriv i u y)]
  have hPcont (w : Spacetime n → ℝ) (hw : ContDiff ℝ ∞ w) : ContinuousOn (P w) K := by
    apply (contDiff_timeDeriv hw).continuous.continuousOn.sub
    exact continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      ((ha i j).continuousOn.mono hKU).mul (contDiff_spatialSecond hw i j).continuous.continuousOn))
  have hFi : IntegrableOn F K := by
    apply ContinuousOn.integrableOn_compact hK
    exact (((hPcont u hu).pow 2).add (hu.continuous.continuousOn.pow 2)).add
      (continuousOn_finsetSum _ (fun i _ => (contDiff_spatialDeriv hu i).continuous.continuousOn.pow 2))
  have hPi : IntegrableOn (fun y => P v y ^ 2) K :=
    ((hPcont v hv).pow 2).integrableOn_compact hK
  have hbound := integral_mono_ae hPi (hFi.const_mul (3 * L))
    (by filter_upwards [ae_restrict_mem hK.measurableSet] with y hy; exact hpoint y hy)
  rw [integral_const_mul] at hbound
  have houtside (y : Spacetime n) (hy : y ∉ K) : P v y = 0 := by
    have hnot : y ∉ tsupport v := fun h => hy (hχK ▸ hvs h)
    have ht : timeDeriv v y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hnot ((tsupport_fderiv_apply_subset ℝ (0, 1)) h))
    have hd (i j : Fin n) : spatialSecond i j v y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hnot (((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans
        (tsupport_fderiv_apply_subset ℝ (spatialDirection j))) h))
    simp only [P, ht, hd, mul_zero, Finset.sum_const_zero, sub_self]
  have hrestrict : (∫ y in K, P v y ^ 2) = ∫ y, P v y ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [houtside y hy]; norm_num)
  rw [hrestrict] at hbound
  have henergy := hcoercive v hv hvc (hvs.trans hχs)
  have heq : EqOn v u (ball z (s / 4)) := by
    intro y hy
    change χ y * u y = u y
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  have htime (y : Spacetime n) (hy : y ∈ ball z (s / 4)) : timeDeriv u y = timeDeriv v y := by
    exact congrArg (fun A : Spacetime n →L[ℝ] ℝ => A (0, 1))
      (heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hy)).fderiv_eq.symm
  have hsecond (i j : Fin n) (y : Spacetime n) (hy : y ∈ ball z (s / 4)) :
      spatialSecond i j u y = spatialSecond i j v y := by
    have he : EqOn (spatialDeriv j v) (spatialDeriv j u) (ball z (s / 4)) := by
      intro x hx
      exact congrArg (fun A : Spacetime n →L[ℝ] ℝ => A (spatialDirection j))
        (heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)).fderiv_eq
    exact congrArg (fun A : Spacetime n →L[ℝ] ℝ => A (spatialDirection i))
      (he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hy)).fderiv_eq.symm
  have htbound : (∫ y in ball z (s / 4), timeDeriv u y ^ 2) ≤ ∫ y, timeDeriv v y ^ 2 := by
    rw [setIntegral_congr_fun isOpen_ball.measurableSet (fun y hy => by rw [htime y hy])]
    exact setIntegral_le_integral (integrable_timeDeriv_sq hv hvc)
      (Eventually.of_forall (fun y => sq_nonneg _))
  have hdbound : (∫ y in ball z (s / 4), ∑ i, ∑ j, spatialSecond i j u y ^ 2) ≤
      ∫ y, ∑ i, ∑ j, spatialSecond i j v y ^ 2 := by
    have he : (∫ y in ball z (s / 4), ∑ i, ∑ j, spatialSecond i j u y ^ 2) =
        ∫ y in ball z (s / 4), ∑ i, ∑ j, spatialSecond i j v y ^ 2 := by
      apply setIntegral_congr_fun isOpen_ball.measurableSet
      intro y hy
      simp_rw [hsecond _ _ y hy]
    rw [he]
    exact setIntegral_le_integral
      (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        integrable_spatialSecond_sq hv hvc i j)))
      (Eventually.of_forall (fun y => Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => sq_nonneg _))))
  have hfinal := (add_le_add htbound (mul_le_mul_of_nonneg_left hdbound
    (by positivity : 0 ≤ κ ^ 2 / 2))).trans henergy
  have htarget : closedBall z (2 * (s / 4)) = K := by dsimp only [K]; congr 1; ring
  rw [htarget]
  change _ ≤ 6 * L * ∫ y in K, F y
  change _ ≤ 2 * ∫ y, P v y ^ 2 at hfinal
  nlinarith

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
