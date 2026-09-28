import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.HilbertExtraction
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakDerivativeClosure












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness




theorem m64Bounded_pointwise_l2_tendsto
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {mu : Measure X} [IsFiniteMeasure mu]
    (f : ℕ → X → E) (u : X → E) (hf : ∀ j, MemLp (f j) 2 mu) (hu : MemLp u 2 mu)
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ j x, ‖f j x‖ ≤ R)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun j => f j x) atTop (𝓝 (u x))) :
    Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hu.toLp u)) := by
  have hub : ∀ᵐ x ∂mu, ‖u x‖ ≤ R := hlim.mono fun x hx =>
    le_of_tendsto hx.norm (Eventually.of_forall fun j => hb j x)
  have hdom (j : ℕ) : ∀ᵐ x ∂mu, ‖‖f j x - u x‖ ^ 2‖ ≤ (2 * R) ^ 2 := by
    filter_upwards [hub] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    exact (norm_sub_le _ _).trans (by linarith [hb j x])
  have hpoint : ∀ᵐ x ∂mu, Tendsto (fun j => ‖f j x - u x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (hx.sub_const (u x)).norm.pow 2
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ : X => (2 * R) ^ 2)
    (fun j => ((hf j).aestronglyMeasurable.sub hu.aestronglyMeasurable).norm.pow 2)
    (integrable_const _) hdom hpoint
  have heq (j : ℕ) : ‖(hf j).toLp (f j) - hu.toLp u‖ ^ 2 =
      ∫ x, ‖f j x - u x‖ ^ 2 ∂mu := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf j).toLp (f j)) (hu.toLp u),
      (hf j).coeFn_toLp, hu.coeFn_toLp] with x hx hfx hux
    simp only [hx, Pi.sub_apply, hfx, hux]
  have hsq : Tendsto (fun j => ‖(hf j).toLp (f j) - hu.toLp u‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [heq, integral_zero, Pi.pow_apply, Pi.sub_apply] using hDCT
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt



theorem m64Weak_limit_norm_sq_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u : ℕ → H} {v : H} (hu : WeakConverges u v)
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B)) (hbound : ∀ j, ‖u j‖ ^ 2 ≤ b j) :
    ‖v‖ ^ 2 ≤ B := by
  have hl := (hu ((innerSL ℝ) v)).const_mul 2 |>.sub_const (‖v‖ ^ 2)
  have hlim : Tendsto (fun j => 2 * inner ℝ v (u j) - ‖v‖ ^ 2) atTop (𝓝 (‖v‖ ^ 2)) := by
    simpa only [innerSL_apply_apply, real_inner_self_eq_norm_sq, two_mul,
      add_sub_cancel_right] using hl
  apply le_of_tendsto_of_tendsto hlim hb
  exact Eventually.of_forall fun j => (show 2 * inner ℝ v (u j) - ‖v‖ ^ 2 ≤ ‖u j‖ ^ 2 by
    nlinarith [real_inner_le_norm v (u j), sq_nonneg (‖u j‖ - ‖v‖)]).trans (hbound j)

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)



theorem m64Plane_two_columns_subsequence
    {S : Set LoopPlane} (V : ℕ → Fin 2 → LoopPlane → E)
    (hV : ∀ j i, MemLp (V j i) 2 (volume.restrict S))
    {C : ℝ} (hC : ∀ j i, (∫ p in S, ‖V j i p‖ ^ 2) ≤ C) :
    ∃ (k : ℕ → ℕ) (W : Fin 2 → Lp E 2 (volume.restrict S)), StrictMono k ∧
      ∀ i, WeakConverges (fun j => (hV (k j) i).toLp (V (k j) i)) (W i) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hnorm (j : ℕ) (i : Fin 2) :
      ‖(hV j i).toLp (V j i)‖ ≤ Real.sqrt (max C 0) := by
    apply Real.le_sqrt_of_sq_le
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    calc
      _ = ∫ p in S, ‖V j i p‖ ^ 2 := integral_congr_ae
        ((hV j i).coeFn_toLp.mono fun p hp => congrArg (fun v : E => ‖v‖ ^ 2) hp)
      _ ≤ C := hC j i
      _ ≤ max C 0 := le_max_left _ _
  obtain ⟨w0, k0, hk0, hw0⟩ := m64SeparableHilbert_weak_subsequence
    (fun j => (hV j 0).toLp (V j 0)) (fun j => hnorm j 0)
  obtain ⟨w1, k1, hk1, hw1⟩ := m64SeparableHilbert_weak_subsequence
    (fun j => (hV (k0 j) 1).toLp (V (k0 j) 1)) (fun j => hnorm (k0 j) 1)
  refine ⟨k0 ∘ k1, ![w0, w1], hk0.comp hk1, ?_⟩
  intro i
  fin_cases i
  · exact fun L => (hw0 L).comp hk1.tendsto_atTop
  · exact hw1

private theorem coordinate_test_apply
    {S : Set LoopPlane} (phi : LoopPlane → ℝ) (hp : MemLp phi 2 (volume.restrict S))
    (b : Fin m) (u : Lp E 2 (volume.restrict S)) :
    testIntegral phi hp (LpFiniteCoordinatesNative.coordinateLp (volume.restrict S) b u) =
      ∫ p in S, phi p * u p b := by
  rw [testIntegral_apply]
  apply integral_congr_ae
  filter_upwards [LpFiniteCoordinatesNative.coordinateLp_coe (volume.restrict S) b u]
    with p hp
  simp only [hp, smul_eq_mul]



theorem m64Plane_weak_partial_closed
    {S : Set LoopPlane} {u v : ℕ → Lp E 2 (volume.restrict S)}
    {U V : Lp E 2 (volume.restrict S)}
    (hu : WeakConverges u U) (hv : WeakConverges v V) (i : Fin 2) (b : Fin m)
    (hw : ∀ j, HasWeakPartialDeriv i (fun p => v j p b) (fun p => u j p b) S) :
    HasWeakPartialDeriv i (fun p => V p b) (fun p => U p b) S := by
  intro phi hphi hc hs
  let dphi : LoopPlane → ℝ := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hp : MemLp phi 2 (volume.restrict S) :=
    (hphi.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdp : MemLp dphi 2 (volume.restrict S) :=
    (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).mono_measure Measure.restrict_le_self
  let P := LpFiniteCoordinatesNative.coordinateLp (volume.restrict S) b
  have hup : WeakConverges (fun j => P (u j)) (P U) := fun L => hu (L.comp P)
  have hvp : WeakConverges (fun j => P (v j)) (P V) := fun L => hv (L.comp P)
  have hlim := weak_limit_linear_identity hvp hup
    (testIntegral (F := ℝ) dphi hdp) (testIntegral phi hp) (fun j => by
      rw [coordinate_test_apply, coordinate_test_apply]
      simpa only [dphi, mul_comm] using hw j phi hphi hc hs)
  rw [coordinate_test_apply, coordinate_test_apply] at hlim
  simpa only [dphi, mul_comm] using hlim



theorem m64Plane_c1_weak_partial
    {S : Set LoopPlane} (hS : IsOpen S) {f : LoopPlane → E} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (b : Fin m) : HasWeakPartialDeriv i
      (fun p => (fderiv ℝ f p (EuclideanSpace.single i 1)) b) (fun p => f p b) S := by
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) b
  have hb : ContDiff ℝ 1 (fun p => f p b) := P.contDiff.comp hf
  have hweak := HasWeakPartialDeriv.of_contDiff (Ω := S) hS (i := i) hb
  have hd : (fun p => fderiv ℝ (fun q => f q b) p (EuclideanSpace.single i 1)) =
      fun p => (fderiv ℝ f p (EuclideanSpace.single i 1)) b := by
    funext p
    have hh := (P.hasFDerivAt.comp p (hf.differentiable (by simp) p).hasFDerivAt).fderiv
    exact congrArg (fun L => L (EuclideanSpace.single i 1)) hh
  rwa [hd] at hweak

end PoincareConjecture
