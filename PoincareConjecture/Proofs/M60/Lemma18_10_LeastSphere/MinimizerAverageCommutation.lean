import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAverageBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem kernel_assoc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {φ ψ : Plane → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    {u : Plane → E} (hu : LocallyIntegrable u volume) (x : Plane) :
    (φ ⋆[lsmul ℝ ℝ, volume] (ψ ⋆[lsmul ℝ ℝ, volume] u)) x =
      ((φ ⋆[mul ℝ ℝ, volume] ψ) ⋆[lsmul ℝ ℝ, volume] u) x := by
  have huNorm : LocallyIntegrable (fun y => ‖u y‖) volume :=
    fun y => (hu y).norm
  have hnorm := hcψ.norm.continuous_convolution_left (mul ℝ ℝ) hψ.norm huNorm
  apply (convolution_assoc (mul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ)
    (fun a b v => by simp only [mul_apply', lsmul_apply, mul_smul])
    hφ.aestronglyMeasurable hψ.aestronglyMeasurable hu.aestronglyMeasurable
    (Eventually.of_forall fun y =>
      hcφ.convolutionExists_left (mul ℝ ℝ) hφ hψ.locallyIntegrable y)
    (Eventually.of_forall fun y =>
      hcψ.norm.convolutionExists_left (mul ℝ ℝ) hψ.norm huNorm y)
    (hcφ.norm.convolutionExists_left (mul ℝ ℝ) hφ.norm hnorm.locallyIntegrable x)).symm

theorem suConvolution_kernel_commute {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {φ ψ : Plane → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    {u : Plane → E} (hu : LocallyIntegrable u volume) (x : Plane) :
    (φ ⋆[lsmul ℝ ℝ, volume] (ψ ⋆[lsmul ℝ ℝ, volume] u)) x =
      (ψ ⋆[lsmul ℝ ℝ, volume] (φ ⋆[lsmul ℝ ℝ, volume] u)) x := by
  rw [kernel_assoc hφ hcφ hψ hcψ hu, kernel_assoc hψ hcψ hφ hcφ hu]
  have hcomm : φ ⋆[mul ℝ ℝ, volume] ψ = ψ ⋆[mul ℝ ℝ, volume] φ := by
    ext y
    rw [convolution_mul, convolution_mul_swap]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => mul_comm _ _
  rw [hcomm]

theorem suMollifier_successive_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : Plane → E} (hu : LocallyIntegrable u volume)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r) (hr1 : r ≤ 1 / 16)
    {Lr Ls : ℝ} (hLr : 0 ≤ Lr) (hLs : 0 ≤ Ls)
    (hlipr : ∀ x ∈ Metric.closedBall (0 : Plane) (3 / 4),
      ∀ y ∈ Metric.closedBall (0 : Plane) (3 / 4),
      dist ((mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u) x)
        ((mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u) y) ≤ Lr * dist x y)
    (hlips : ∀ x ∈ Metric.closedBall (0 : Plane) (3 / 4),
      ∀ y ∈ Metric.closedBall (0 : Plane) (3 / 4),
      dist ((mollifierEps hs ⋆[lsmul ℝ ℝ, volume] u) x)
        ((mollifierEps hs ⋆[lsmul ℝ ℝ, volume] u) y) ≤ Ls * dist x y)
    (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) (1 / 2)) :
    dist ((mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u) x)
      ((mollifierEps hs ⋆[lsmul ℝ ℝ, volume] u) x) ≤ (Lr + Ls) * r := by
  let vr := mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u
  let vs := mollifierEps hs ⋆[lsmul ℝ ℝ, volume] u
  have hvr : Continuous vr :=
    (mollifierEps_compactSupport hr).continuous_convolution_left (lsmul ℝ ℝ)
      (mollifierEps_continuous hr) hu
  have hvs : Continuous vs :=
    (mollifierEps_compactSupport hs).continuous_convolution_left (lsmul ℝ ℝ)
      (mollifierEps_continuous hs) hu
  have hx' : x ∈ Metric.closedBall (0 : Plane) (3 / 4) :=
    Metric.closedBall_subset_closedBall (by norm_num) hx
  have hsub {t : ℝ} (ht : t ≤ r) :
      Metric.ball x t ⊆ Metric.closedBall (0 : Plane) (3 / 4) := by
    intro y hy
    have hy' := Metric.mem_ball.mp hy
    have hx0 := Metric.mem_closedBall.mp hx
    exact Metric.mem_closedBall.mpr (by linarith [dist_triangle y x (0 : Plane)])
  have hfirst : dist ((mollifierEps hs ⋆[lsmul ℝ ℝ, volume] vr) x) (vr x) ≤ Lr * r := by
    apply (mollifierBumpEps hs).dist_normed_convolution_le hvr.aestronglyMeasurable
    intro y hy
    exact (hlipr y (hsub hsr hy) x hx').trans
      (mul_le_mul_of_nonneg_left ((Metric.mem_ball.mp hy).le.trans hsr) hLr)
  have hsecond : dist ((mollifierEps hr ⋆[lsmul ℝ ℝ, volume] vs) x) (vs x) ≤ Ls * r := by
    apply (mollifierBumpEps hr).dist_normed_convolution_le hvs.aestronglyMeasurable
    intro y hy
    exact (hlips y (hsub le_rfl hy) x hx').trans
      (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le hLs)
  have hmid : (mollifierEps hs ⋆[lsmul ℝ ℝ, volume] vr) x =
      (mollifierEps hr ⋆[lsmul ℝ ℝ, volume] vs) x :=
    suConvolution_kernel_commute (mollifierEps_continuous hs) (mollifierEps_compactSupport hs)
      (mollifierEps_continuous hr) (mollifierEps_compactSupport hr) hu x
  calc
    dist (vr x) (vs x) ≤
        dist (vr x) ((mollifierEps hs ⋆[lsmul ℝ ℝ, volume] vr) x) +
          dist ((mollifierEps hs ⋆[lsmul ℝ ℝ, volume] vr) x) (vs x) := dist_triangle _ _ _
    _ ≤ Lr * r + Ls * r := add_le_add (by simpa only [dist_comm] using hfirst)
      (by rw [hmid]; exact hsecond)
    _ = _ := by ring

end PoincareConjecture.M60

end
