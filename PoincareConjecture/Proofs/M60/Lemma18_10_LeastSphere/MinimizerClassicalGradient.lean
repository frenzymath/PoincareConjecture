import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAverageDerivative
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

def suPlaneColumns {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Fin 2 → E) : Plane →L[ℝ] E :=
  (EuclideanSpace.proj (𝕜 := ℝ) 0).smulRight (p 0) +
    (EuclideanSpace.proj (𝕜 := ℝ) 1).smulRight (p 1)

theorem suPlaneColumns_reconstruct {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Plane →L[ℝ] E) :
    suPlaneColumns (fun i => L (EuclideanSpace.single i 1)) = L := by
  ext x
  have hx : x = x 0 • EuclideanSpace.single 0 1 + x 1 • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  change x 0 • L (EuclideanSpace.single 0 1) + x 1 • L (EuclideanSpace.single 1 1) = L x
  nth_rw 3 [hx]
  simp

theorem suMollifier_joint_tendsto {m : ℕ} {r : ℕ → ℝ} (hr : ∀ j, 0 < r j)
    (hz : Tendsto r atTop (𝓝 0)) {g : Plane → EuclideanSpace ℝ (Fin m)}
    (hg : AEStronglyMeasurable g volume) {x : Plane} (hc : ContinuousAt g x) :
    Tendsto (fun q : ℕ × Plane =>
      (mollifierEps (hr q.1) ⋆[lsmul ℝ ℝ, volume] g) q.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (g x)) := by
  exact ContDiffBump.convolution_tendsto_right
    (φ := fun q : ℕ × Plane => mollifierBumpEps (hr q.1))
    (g := fun _ : ℕ × Plane => g) (hz.comp tendsto_fst)
    (Eventually.of_forall fun _ => hg) (hc.tendsto.comp tendsto_snd) tendsto_snd

theorem suContinuous_weak_gradient_hasFDerivAt_on_ball {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    {a : Plane} {R : ℝ} (hR : 0 < R)
    (hu : MemLp u 2 (volume.restrict (Metric.ball a R)))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball a R)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun y => p i y b) (fun y => u y b)
      (Metric.ball a R))
    (huc : ContinuousOn u (Metric.ball a R))
    (hpc : ∀ i, ContinuousOn (p i) (Metric.ball a R))
    (x : Plane) (hx : x ∈ Metric.ball a (R / 2)) :
    HasFDerivAt u (suPlaneColumns (fun i => p i x)) x := by
  let O : Set Plane := Metric.ball a R
  let U := O.indicator u
  let P : Fin 2 → Plane → EuclideanSpace ℝ (Fin m) := fun i => O.indicator (p i)
  have hU : LocallyIntegrable U volume := suDisk_indicator_locallyIntegrable hu
  have hP (i) : LocallyIntegrable (P i) volume := suDisk_indicator_locallyIntegrable (hp i)
  have hsub : Metric.ball a (R / 2) ⊆ O := Metric.ball_subset_ball (by linarith)
  have hUc (y : Plane) (hy : y ∈ O) : ContinuousAt U y := by
    have he : U =ᶠ[𝓝 y] u := eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hy)
      (fun z hz => indicator_of_mem hz u)
    exact (huc.continuousAt (Metric.isOpen_ball.mem_nhds hy)).congr_of_eventuallyEq he
  have hPc (i : Fin 2) (y : Plane) (hy : y ∈ O) : ContinuousAt (P i) y := by
    have he : P i =ᶠ[𝓝 y] p i := eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hy)
      (fun z hz => indicator_of_mem hz (p i))
    exact ((hpc i).continuousAt (Metric.isOpen_ball.mem_nhds hy)).congr_of_eventuallyEq he
  let r : ℕ → ℝ := fun j => (R / 16) * (1 / 16 : ℝ) ^ j
  have hr (j : ℕ) : 0 < r j := mul_pos (by positivity) (pow_pos (by norm_num) _)
  have hr1 (j : ℕ) : r j ≤ R / 16 := by
    dsimp only [r]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num))
  have hrz : Tendsto r atTop (𝓝 0) := by
    simpa only [r, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
        (by norm_num : (1 / 16 : ℝ) < 1)).const_mul (R / 16)
  let v : ℕ → Plane → EuclideanSpace ℝ (Fin m) := fun j =>
    mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] U
  let V : ℕ → Plane → Plane →L[ℝ] EuclideanSpace ℝ (Fin m) := fun j y =>
    suPlaneColumns (fun i => (mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] P i) y)
  have hv (j : ℕ) : ContDiff ℝ ∞ (v j) :=
    (mollifierEps_compactSupport (hr j)).contDiff_convolution_left (lsmul ℝ ℝ)
      (mollifierEps_smooth (hr j)) hU
  have hd (j : ℕ) (y : Plane) (hy : y ∈ Metric.ball a (R / 2)) :
      fderiv ℝ (v j) y = V j y := by
    have hsupport : tsupport (fun z => mollifierEps (hr j) (y - z)) ⊆ O := by
      rw [suMollifier_translated_tsupport (hr j) y]
      intro z hz
      have hz' := Metric.mem_closedBall.mp hz
      have hy' := Metric.mem_ball.mp hy
      exact Metric.mem_ball.mpr (by linarith [dist_triangle z y a, hr1 j])
    rw [← suPlaneColumns_reconstruct (fderiv ℝ (v j) y)]
    apply congrArg suPlaneColumns
    funext i
    exact suWeak_convolution_fderiv Metric.isOpen_ball.measurableSet (hw i)
      hU (hP i) (mollifierEps_smooth (hr j)) (mollifierEps_compactSupport (hr j)) y hsupport
  have hcol (i : Fin 2) := suMollifier_joint_tendsto hr hrz
    (hP i).aestronglyMeasurable (hPc i x (hsub hx))
  have hT (i : Fin 2) :=
    ((ContinuousLinearMap.smulRightL ℝ Plane (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace.proj (𝕜 := ℝ) i)).continuous.tendsto (P i x)).comp (hcol i)
  have hV : Tendsto (fun q : ℕ × Plane => V q.1 q.2) (atTop ×ˢ 𝓝 x)
      (𝓝 (suPlaneColumns (fun i => p i x))) := by
    simpa only [V, suPlaneColumns, ContinuousLinearMap.smulRightL_apply_apply,
      Function.comp_apply, P, indicator_of_mem (hsub hx)] using (hT 0).add (hT 1)
  have hVuniform : TendstoUniformlyOnFilter V
      (fun _ => suPlaneColumns (fun i => p i x)) atTop (𝓝 x) :=
    (tendsto_const_nhds.prodMk hV).mono_right (by
      rw [← nhds_prod_eq]
      exact nhds_le_uniformity _)
  apply hasFDerivAt_of_tendstoUniformlyOnFilter hVuniform
  · filter_upwards [tendsto_snd.eventually (Metric.isOpen_ball.mem_nhds hx)] with q hq
    rw [← hd q.1 q.2 hq]
    exact ((hv q.1).differentiable (by simp) q.2).hasFDerivAt
  · filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    have h := ContDiffBump.convolution_tendsto_right
      (φ := fun j => mollifierBumpEps (hr j)) (g := fun _ : ℕ => U) hrz
      (Eventually.of_forall fun _ => hU.aestronglyMeasurable)
      ((hUc y (hsub hy)).tendsto.comp tendsto_snd) (tendsto_const_nhds (x := y))
    simpa only [v, U, mollifierEps, indicator_of_mem (hsub hy)] using! h

theorem suContinuous_weak_gradient_hasFDerivAt {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hu : MemLp u 2 (volume.restrict (Metric.ball 0 2)))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 2)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun y => p i y b) (fun y => u y b)
      (Metric.ball 0 2))
    (huc : ContinuousOn u (Metric.ball 0 2))
    (hpc : ∀ i, ContinuousOn (p i) (Metric.ball 0 2))
    (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) 1) :
    HasFDerivAt u (suPlaneColumns (fun i => p i x)) x :=
  suContinuous_weak_gradient_hasFDerivAt_on_ball (by norm_num) hu hp hw huc hpc x
    (by simpa using hx)

end PoincareConjecture.M60

end
