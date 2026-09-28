import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalFluxExtension
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSourceWeakChain










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff ENNReal

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak



theorem suQuadraticDerivative_comp_linear
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : F → H} (hA : ContDiff ℝ 1 A) {C : ℝ} (hC : 0 < C)
    (hDA : ∀ z, ‖fderiv ℝ A z‖ ≤ C * (1 + ‖z‖ ^ 2)) (L : E →L[ℝ] F) :
    ∃ D : ℝ, 0 < D ∧ ∀ z, ‖fderiv ℝ (A ∘ L) z‖ ≤ D * (1 + ‖z‖ ^ 2) := by
  let B := ‖L‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L]
  have hLB : ‖L‖ ≤ B := by dsimp [B]; linarith
  refine ⟨C * B ^ 3, by positivity, fun z => ?_⟩
  rw [fderiv_comp z (hA.differentiable (by norm_num) _) L.differentiableAt, L.fderiv]
  have hz : ‖L z‖ ≤ B * ‖z‖ := (L.le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hLB (norm_nonneg z))
  have hz2 : 1 + ‖L z‖ ^ 2 ≤ B ^ 2 * (1 + ‖z‖ ^ 2) := by
    have hsq := sq_le_sq₀ (norm_nonneg (L z)) (by positivity) |>.mpr hz
    nlinarith [sq_nonneg (B - 1)]
  calc
    _ ≤ ‖fderiv ℝ A (L z)‖ * ‖L‖ := opNorm_comp_le _ _
    _ ≤ (C * (1 + ‖L z‖ ^ 2)) * B := mul_le_mul (hDA _) hLB
      (norm_nonneg _) (by positivity)
    _ ≤ (C * (B ^ 2 * (1 + ‖z‖ ^ 2))) * B := by gcongr
    _ = _ := by ring




theorem suQuadraticDerivative_integrable
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X} [IsFiniteMeasure μ]
    {u W : X → E} (hu : MemLp u 4 μ) (hW : MemLp W 2 μ)
    {A : E → F} (hA : ContDiff ℝ 1 A) {C : ℝ} (hC : 0 < C)
    (hDA : ∀ z, ‖fderiv ℝ A z‖ ≤ C * (1 + ‖z‖ ^ 2)) :
    Integrable (fun x => fderiv ℝ A (u x) (W x)) μ := by
  have hu4 : MemLp (fun x => ‖u x‖ ^ 4) 1 μ := by
    simpa using hu.norm_rpow (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)
  have hW2 : MemLp (fun x => ‖W x‖ ^ 2) 1 μ := by
    simpa using hW.norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
  have hc : Continuous (fun z : E × E => fderiv ℝ A z.1 z.2) :=
    ((hA.continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply continuous_snd
  have hm := hc.comp_aestronglyMeasurable (hu.1.prodMk hW.1)
  apply memLp_one_iff_integrable.mp
  apply ((((memLp_const (1 : ℝ)).add hu4).add hW2).const_mul C).of_le hm
  filter_upwards [] with x
  have hb := (fderiv ℝ A (u x)).le_opNorm (W x) |>.trans
    (mul_le_mul_of_nonneg_right (hDA _) (norm_nonneg _))
  have hy : (1 + ‖u x‖ ^ 2) * ‖W x‖ ≤ 1 + ‖u x‖ ^ 4 + ‖W x‖ ^ 2 := by
    nlinarith only [sq_nonneg (‖W x‖ - 1), sq_nonneg (‖W x‖ - ‖u x‖ ^ 2)]
  simp only [Pi.add_apply, Real.norm_of_nonneg (by positivity :
    0 ≤ C * (1 + ‖u x‖ ^ 4 + ‖W x‖ ^ 2))]
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hy hC.le])



theorem suWeakPartial_pair_comp_quadratic {p q : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin p)}
    {v : LoopPlane → EuclideanSpace ℝ (Fin q)}
    {U : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin p)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin q)}
    {a : LoopPlane} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : MemLp u 4 (volume.restrict (Metric.ball a R)))
    (hv : MemLp v 4 (volume.restrict (Metric.ball a R)))
    (hU : ∀ i, MemLp (U i) 2 (volume.restrict (Metric.ball a R)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (Metric.ball a R)))
    (hwu : ∀ i b, HasWeakPartialDeriv i (fun x => U i x b) (fun x => u x b)
      (Metric.ball a R))
    (hwv : ∀ i b, HasWeakPartialDeriv i (fun x => V i x b) (fun x => v x b)
      (Metric.ball a R))
    {A : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) → ℝ}
    (hA : ContDiff ℝ 1 A) {C : ℝ} (hC : 0 < C)
    (hDA : ∀ z, ‖fderiv ℝ A z‖ ≤ C * (1 + ‖z‖ ^ 2)) (i : Fin 2) :
    IntegrableOn (fun x => fderiv ℝ A (u x, v x) (U i x, V i x)) (Metric.ball a R) ∧
      HasWeakPartialDeriv i (fun x => fderiv ℝ A (u x, v x) (U i x, V i x))
        (fun x => A (u x, v x)) (Metric.ball a r) := by
  let e : EuclideanSpace ℝ (Fin (p + q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) := EuclideanSpace.finAddEquivProd
  let w : LoopPlane → EuclideanSpace ℝ (Fin (p + q)) := fun x => e.symm (u x, v x)
  let W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin (p + q)) :=
    fun j x => e.symm (U j x, V j x)
  let : IsFiniteMeasure (volume.restrict (Metric.ball a R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball a R) < ⊤)⟩
  have huw : MemLp w 4 (volume.restrict (Metric.ball a R)) :=
    e.symm.toContinuousLinearMap.comp_memLp' (memLp_prod_iff.mpr ⟨hu, hv⟩)
  have hW (j : Fin 2) : MemLp (W j) 2 (volume.restrict (Metric.ball a R)) :=
    e.symm.toContinuousLinearMap.comp_memLp' (memLp_prod_iff.mpr ⟨hU j, hV j⟩)
  have hw (j : Fin 2) (b : Fin (p + q)) : HasWeakPartialDeriv j
      (fun x => W j x b) (fun x => w x b) (Metric.ball a R) := by
    cases b using Fin.addCases with
    | left k => simpa only [W, w, e, suFinAddEquivProd_symm_left] using hwu j k
    | right k => simpa only [W, w, e, suFinAddEquivProd_symm_right] using hwv j k
  obtain ⟨D, hD, hb⟩ := suQuadraticDerivative_comp_linear hA hC hDA e.toContinuousLinearMap
  have ht := suWeakPartial_comp_quadratic hr hrR huw hW hw (hA.comp e.contDiff) hD hb i
  have hi := suQuadraticDerivative_integrable huw (hW i) (hA.comp e.contDiff) hD hb
  have he (x : LoopPlane) : fderiv ℝ (A ∘ e) (w x) (W i x) =
      fderiv ℝ A (u x, v x) (U i x, V i x) := by
    rw [e.comp_right_fderiv]
    simp [w, W]
  exact ⟨by simpa only [IntegrableOn, he] using! hi,
    by simpa only [he, Function.comp_apply, w, e.apply_symm_apply] using ht⟩

end PoincareConjecture.M60

end
