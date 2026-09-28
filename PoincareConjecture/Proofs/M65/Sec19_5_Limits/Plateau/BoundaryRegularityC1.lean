import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingWeak
import Mathlib.Analysis.Calculus.UniformLimitsDeriv












set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap InnerProductSpace

namespace PoincareConjecture.M65Boundary

open M65Interior

private theorem continuous_average_uniform {u f : LoopPlane → ℝ}
    (hu : LocallyIntegrable u volume) {U : Set LoopPlane} (hU : IsOpen U)
    (hf : ContinuousOn f U) (heq : u =ᵐ[volume.restrict U] f)
    {p : LoopPlane} {R : ℝ} (hR : 0 < R) (hsub : closedBall p (2 * R) ⊆ U) :
    TendstoUniformlyOn (fun r x => averagingValue u r x) f (𝓝[>] 0) (ball p R) := by
  have hfc : UniformContinuousOn f (closedBall p (2 * R)) :=
    (isCompact_closedBall p (2 * R)).uniformContinuousOn_of_continuous (hf.mono hsub)
  have heq' : ∀ᵐ z ∂volume, z ∈ U → u z = f z := (ae_restrict_iff' hU.measurableSet).mp heq
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hfc (ε / 2) (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hR hδ)] with r hr x hx
  have hrR : r < R := hr.2.trans_le (min_le_left _ _)
  have hrδ : r < δ := hr.2.trans_le (min_le_right _ _)
  let k := fun z : LoopPlane => averagingKernel r (x - z)
  have hk : Integrable k := by
    exact (averagingKernel_hasCompactSupport hr.1).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ)
        (continuous_const : Continuous (fun _ : LoopPlane => (1 : ℝ))).locallyIntegrable
        (averagingKernel_contDiff r).continuous x |>.congr
          (ae_of_all _ fun z => one_mul _)
  have hmass : (∫ z, k z) = 1 := by
    change (∫ z, averagingKernel r (x - z)) = 1
    rw [integral_sub_left_eq_self, averagingKernel_integral hr.1]
  have hui := averagingValue_integrable hu hr.1 x
  have hi : Integrable (fun z => k z * (u z - f x)) := by
    apply (hui.sub (hk.mul_const (f x))).congr
    filter_upwards [] with z
    change u z * k z - k z * f x = _
    ring
  have hid : averagingValue u r x - f x = ∫ z, k z * (u z - f x) := by
    calc
      _ = (∫ z, u z * k z) - ∫ z, k z * f x := by rw [integral_mul_const, hmass, one_mul]; rfl
      _ = ∫ z, u z * k z - k z * f x := (integral_sub hui (hk.mul_const _)).symm
      _ = _ := integral_congr_ae (ae_of_all _ fun z => by ring)
  have hbound : ∀ᵐ z ∂volume, ‖k z * (u z - f x)‖ ≤ k z * (ε / 2) := by
    filter_upwards [heq'] with z hz
    by_cases hkz : k z = 0
    · simp only [hkz, zero_mul, norm_zero, le_refl]
    have hdist : dist x z ≤ r := by
      exact mem_closedBall_zero_iff.mp (averagingKernel_support hr.1 hkz)
    have hx' : x ∈ closedBall p (2 * R) :=
      closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hx)
    have hz' : z ∈ closedBall p (2 * R) := by
      apply mem_closedBall.mpr
      have hxp := mem_ball.mp hx
      calc
        dist z p ≤ dist z x + dist x p := dist_triangle _ _ _
        _ ≤ 2 * R := by rw [dist_comm z x]; linarith
    rw [hz (hsub hz'), norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (averagingKernel_nonneg r (x - z))]
    apply mul_le_mul_of_nonneg_left _ (averagingKernel_nonneg r (x - z))
    exact (hclose z hz' x hx' (by simpa only [dist_comm] using hdist.trans_lt hrδ)).le
  have hnorm : ‖averagingValue u r x - f x‖ ≤ ε / 2 := by
    rw [hid]
    calc
      _ ≤ ∫ z, ‖k z * (u z - f x)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, k z * (ε / 2) := integral_mono_ae hi.norm (hk.mul_const _) hbound
      _ = ε / 2 := by rw [integral_mul_const, hmass, one_mul]
  rw [dist_comm, dist_eq_norm]
  exact hnorm.trans_lt (half_lt_self hε)

private noncomputable def gradientRow (v : Fin 2 → ℝ) : LoopPlane →L[ℝ] ℝ :=
  v 0 • EuclideanSpace.proj 0 + v 1 • EuclideanSpace.proj 1

private theorem average_derivative_row
    (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    fderiv ℝ (averagingValue u r) x = gradientRow (fun i => averagingValue (d i) r x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [← (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have heq := averagingValue_fderiv_of_weak u d hw hr x i
  have hi : (∫ z, averagingKernel r (x - z) * d i z) = averagingValue (d i) r x :=
    integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  rw [heq, hi]
  fin_cases i <;> simp [gradientRow, EuclideanSpace.basisFun_apply]





theorem weak_pair_contDiffOn
    (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    {U : Set LoopPlane} (hU : IsOpen U) (f : LoopPlane → ℝ) (g : Fin 2 → LoopPlane → ℝ)
    (hf : ContinuousOn f U) (hg : ∀ i, ContinuousOn (g i) U)
    (huf : (u : LoopPlane → ℝ) =ᵐ[volume.restrict U] f)
    (hdg : ∀ i, (d i : LoopPlane → ℝ) =ᵐ[volume.restrict U] g i) :
    ContDiffOn ℝ 1 f U ∧ ∀ x ∈ U, ∀ i : Fin 2,
      fderiv ℝ f x (EuclideanSpace.basisFun (Fin 2) ℝ i) = g i x := by
  let D := fun x => gradientRow (fun i => g i x)
  have hD : ContinuousOn D U := (hg 0).smul continuousOn_const |>.add
    ((hg 1).smul continuousOn_const)
  have hdiff : ∀ p ∈ U, HasFDerivAt f (D p) p := by
    intro p hp
    obtain ⟨s, hs, hps⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
    let R := s / 4
    have hR : 0 < R := by dsimp only [R]; positivity
    have hsub : closedBall p (2 * R) ⊆ U :=
      (closedBall_subset_ball (by dsimp only [R]; linarith)).trans hps
    have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
    have hval := continuous_average_uniform hu hU hf huf hR hsub
    have hcoord (i : Fin 2) := continuous_average_uniform
      ((Lp.memLp (d i)).locallyIntegrable (by norm_num)) hU (hg i) (hdg i) hR hsub
    let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
    have hr0 : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall hr⟩
    have hvaln : ∀ x ∈ ball p R, Tendsto (fun n => averagingValue u (r n) x) atTop (𝓝 (f x)) :=
      fun x hx => (hval.tendsto_at hx).comp hr0
    have hgrad : TendstoUniformlyOn (fun n x =>
        fderiv ℝ (averagingValue u (r n)) x) D atTop (ball p R) := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      let B : ℝ := 1 + ‖EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0‖ +
        ‖EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1‖
      have hB : 0 < B := by dsimp only [B]; positivity
      have he : 0 < ε / (2 * B) := div_pos hε (by positivity)
      have h0 := hr0.eventually (Metric.tendstoUniformlyOn_iff.mp (hcoord 0) _ he)
      have h1 := hr0.eventually (Metric.tendstoUniformlyOn_iff.mp (hcoord 1) _ he)
      filter_upwards [h0, h1] with n hn0 hn1 x hx
      rw [dist_comm, dist_eq_norm, average_derivative_row u d hw (hr n) x]
      have heq : gradientRow (fun i => averagingValue (d i) (r n) x) - D x =
          (averagingValue (d 0) (r n) x - g 0 x) • EuclideanSpace.proj 0 +
          (averagingValue (d 1) (r n) x - g 1 x) • EuclideanSpace.proj 1 := by
        dsimp only [gradientRow, D]
        module
      rw [heq]
      have hb0 : |averagingValue (d 0) (r n) x - g 0 x| ≤ ε / (2 * B) := by
        simpa only [Real.dist_eq, abs_sub_comm] using (hn0 x hx).le
      have hb1 : |averagingValue (d 1) (r n) x - g 1 x| ≤ ε / (2 * B) := by
        simpa only [Real.dist_eq, abs_sub_comm] using (hn1 x hx).le
      apply (norm_add_le _ _).trans_lt
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hbound := add_le_add
        (mul_le_mul_of_nonneg_right hb0
          (norm_nonneg (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0)))
        (mul_le_mul_of_nonneg_right hb1
          (norm_nonneg (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1)))
      have hfactor : ε / (2 * B) *
          (‖EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0‖ +
            ‖EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1‖) < ε := by
        dsimp only [B] at hB ⊢
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ (by positivity)).mpr
        nlinarith [norm_nonneg (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0),
          norm_nonneg (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1)]
      exact hbound.trans_lt (by simpa only [mul_add] using hfactor)
    apply hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hgrad
      (fun n x _ => ?_) hvaln (mem_ball_self hR)
    exact ((averagingValue_joint_contDiffAt hu (hr n) x).comp x
      ((contDiffAt_const (c := r n)).prodMk contDiffAt_id)).differentiableAt
      (by simp) |>.hasFDerivAt
  constructor
  · rw [show (1 : ℕ∞ω) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hdiff x hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hD.congr (fun x hx => (hdiff x hx).fderiv)
  · intro x hx i
    rw [(hdiff x hx).fderiv]
    fin_cases i <;> simp [D, gradientRow, EuclideanSpace.basisFun_apply]

end PoincareConjecture.M65Boundary
