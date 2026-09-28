import PoincareConjecture.Proofs.M10.MollifierBasics
import PoincareConjecture.Proofs.M10.ContactSemiconcavity
import Mathlib.Analysis.Convex.Deriv










set_option autoImplicit false

open Set Filter Metric MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem sub_mem_double_ball {x z x₀ : E} {r : ℝ}
    (hx : x ∈ ball x₀ r) (hz : ‖z‖ ≤ r) : x - z ∈ ball x₀ (2 * r) := by
  rw [mem_ball_iff_norm] at hx ⊢
  calc
    ‖x - z - x₀‖ = ‖(x - x₀) - z‖ := by congr 1; abel
    _ ≤ ‖x - x₀‖ + ‖z‖ := norm_sub_le _ _
    _ < r + r := add_lt_add_of_lt_of_le hx hz
    _ = 2 * r := by ring


theorem concaveOn_normed_convolution (κ : ContDiffBump (0 : E))
    {f : E → ℝ} (hf : Continuous f) {x₀ : E} {r : ℝ}
    (hκ : κ.rOut ≤ r) (hconc : ConcaveOn ℝ (ball x₀ (2 * r)) f) :
    ConcaveOn ℝ (ball x₀ r) (κ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  have hex := (κ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
    (μ := μ) (lsmul ℝ ℝ)
    κ.continuous_normed hf.locallyIntegrable
  apply integral_concaveOn_of_integrand_ae (convex_ball _ _) _ (fun x _ ↦ hex x)
  apply Eventually.of_forall
  intro z
  change ConcaveOn ℝ (ball x₀ r) (fun x ↦ κ.normed μ z * f (x - z))
  by_cases hz : κ.normed μ z = 0
  · simp only [hz, zero_mul]
    exact concaveOn_const _ (convex_ball _ _)
  · have hzn : ‖z‖ ≤ r := by
      have hmem : z ∈ Function.support (κ.normed μ) := hz
      rw [κ.support_normed_eq, mem_ball, dist_zero_right] at hmem
      exact hmem.le.trans hκ
    refine ⟨convex_ball _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hsub : (a • x + b • y) - z = a • (x - z) + b • (y - z) := by
      have hsum : a • z + b • z = z := by rw [← add_smul, hab, one_smul]
      calc
        _ = (a • x + b • y) - (a • z + b • z) := by rw [hsum]
        _ = _ := by simp only [smul_sub]; abel
    dsimp only
    rw [hsub]
    have hc := hconc.2 (sub_mem_double_ball hx hzn) (sub_mem_double_ball hy hzn) ha hb hab
    simp only [smul_eq_mul] at hc ⊢
    nlinarith [mul_le_mul_of_nonneg_left hc (κ.nonneg_normed (μ := μ) z)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem second_fderiv_nonpos_of_concaveOn {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hconc : ConcaveOn ℝ U f)
    {x : E} (hx : x ∈ U) (v : E) : fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let A : ℝ →ᵃ[ℝ] E :=
    { toFun := fun t ↦ x + t • v
      linear := (lsmul ℝ ℝ).flip v |>.toLinearMap
      map_vadd' := by intros; simp [add_smul]; abel }
  have hA : Continuous A := by change Continuous (fun t : ℝ ↦ x + t • v); fun_prop
  have h0 : (0 : ℝ) ∈ A ⁻¹' U := by simpa [A] using hx
  have hn : A ⁻¹' U ∈ 𝓝 (0 : ℝ) := (hU.preimage hA).mem_nhds h0
  have hc : ConcaveOn ℝ (A ⁻¹' U) (f ∘ A) := hconc.comp_affineMap A
  have hd : ∀ t ∈ A ⁻¹' U, DifferentiableAt ℝ (f ∘ A) t := by
    intro t ht
    exact ((hf.contDiffAt (hU.mem_nhds ht)).comp t
      (show ContDiffAt ℝ 2 A t by
        change ContDiffAt ℝ 2 (fun s : ℝ ↦ x + s • v) t
        fun_prop)).differentiableAt two_ne_zero
  have h := (hc.antitoneOn_deriv hd).derivWithin_nonpos (x := (0 : ℝ))
  rw [derivWithin_of_mem_nhds hn] at h
  have hsecond := second_deriv_affine_line (hf.contDiffAt (hU.mem_nhds hx)) v
  change deriv (deriv (fun t : ℝ ↦ f (x + t • v))) 0 ≤ 0 at h
  rwa [hsecond] at h

end PoincareConjecture.M10
