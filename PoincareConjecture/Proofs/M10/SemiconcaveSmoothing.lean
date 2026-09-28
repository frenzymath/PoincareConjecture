import PoincareConjecture.Proofs.M10.ConcaveExtension
import PoincareConjecture.Proofs.M10.QuadraticSmoothing
import PoincareConjecture.Proofs.M10.MollifierLocalJets
import PoincareConjecture.Proofs.M10.ShrinkingBump

set_option autoImplicit false

open Set Filter Metric MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution Topology NNReal

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

include μ in

theorem exists_semiconcave_smoothing {u : E → ℝ} {x₀ : E} {r K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hu : ContinuousOn u (ball x₀ (4 * r)))
    (hc : ConcaveOn ℝ (ball x₀ (4 * r)) (fun x ↦ u x - euclideanQuadratic K x)) :
    ∃ (f : ℕ → E → ℝ) (ε : ℕ → ℝ) (G : ℝ), 0 ≤ G ∧
      Tendsto ε atTop (𝓝 0) ∧ (∀ j, 0 ≤ ε j) ∧
      (∀ j, ContDiff ℝ ∞ (f j)) ∧
      (∀ j, ∀ x ∈ ball x₀ r, |f j x - u x| ≤ ε j) ∧
      (∀ j, ∀ x ∈ ball x₀ r, ‖fderiv ℝ (f j) x‖ ≤ G) ∧
      (∀ j, ∀ x ∈ ball x₀ r, ∀ v, fderiv ℝ (fderiv ℝ (f j)) x v v ≤ K * ‖v‖ ^ 2) ∧
      (∀ x ∈ ball x₀ r, ContDiffAt ℝ 2 u x →
        Tendsto (fun j ↦ fderiv ℝ (f j) x) atTop (𝓝 (fderiv ℝ u x)) ∧
        Tendsto (fun j ↦ fderiv ℝ (fderiv ℝ (f j)) x) atTop
          (𝓝 (fderiv ℝ (fderiv ℝ u) x))) := by
  let β := fun x ↦ u x - euclideanQuadratic K x
  have hq := euclideanQuadratic_contDiff (E := E) K
  have hq2 := hq.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)
  obtain ⟨L, g, hg, heq⟩ := exists_lipschitz_extension_of_concave hr
    (hu.sub hq.continuous.continuousOn) hc
  let κ : ℕ → ContDiffBump (0 : E) := shrinkingBump r hr
  let b : ℕ → E → ℝ := fun j ↦ (κ j).normed μ ⋆[lsmul ℝ ℝ, μ] g
  let f : ℕ → E → ℝ := fun j x ↦ b j x + euclideanQuadratic K x
  let ε : ℕ → ℝ := fun j ↦ L * (κ j).rOut
  let G : ℝ := L + K * (‖x₀‖ + r)
  have hk : Tendsto (fun j ↦ (κ j).rOut) atTop (𝓝 0) := shrinkingBump_rOut_tendsto r hr
  have hb (j : ℕ) : ContDiff ℝ ∞ (b j) := normed_convolution_contDiff (κ j) hg.continuous
  have hb2 (j : ℕ) := (hb j).of_le (by decide : (2 : ℕ∞ω) ≤ ∞)
  have hgc : ConcaveOn ℝ (ball x₀ (2 * r)) g :=
    (hc.subset (ball_subset_ball (by linarith)) (convex_ball _ _)).congr heq
  have hbc (j : ℕ) : ConcaveOn ℝ (ball x₀ r) (b j) :=
    concaveOn_normed_convolution (κ j) hg.continuous (shrinkingBump_rOut_le r hr j) hgc
  have hbl (j : ℕ) : LipschitzWith L (b j) := lipschitzWith_normed_convolution (κ j) hg
  have hsmall : ball x₀ r ⊆ ball x₀ (2 * r) := ball_subset_ball (by linarith)
  have herror (j : ℕ) (x : E) (hx : x ∈ ball x₀ r) : |f j x - u x| ≤ ε j := by
    have h := dist_normed_convolution_le_lipschitz (μ := μ) (κ j) hg x
    have he : g x = u x - euclideanQuadratic K x := (heq (hsmall hx)).symm
    have hid : f j x - u x = b j x - g x := by dsimp only [f]; rw [he]; ring
    simpa only [hid, Real.dist_eq, b, ε] using h
  refine ⟨f, ε, G, by dsimp only [G]; positivity, ?_, ?_, ?_, herror, ?_, ?_, ?_⟩
  · simpa only [ε, mul_zero] using (tendsto_const_nhds (x := (L : ℝ))).mul hk
  · intro j
    exact mul_nonneg L.coe_nonneg (κ j).rOut_pos.le
  · intro j
    exact (hb j).add hq
  · intro j x hx
    exact norm_fderiv_add_quadratic_le (hbl j) ((hb2 j).differentiable two_ne_zero) hK hx
  · intro j x hx v
    exact second_fderiv_add_quadratic_le isOpen_ball (hb2 j) (hbc j) hx K v
  · intro x hx hux
    have he : β =ᶠ[𝓝 x] g := heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds (hsmall hx))
    have hgx : ContDiffAt ℝ 2 g x :=
      (hux.sub hq2.contDiffAt).congr_of_eventuallyEq he.symm
    have hj := normed_convolution_local_jets_tendsto (μ := μ) hk hgx
    have hug : u =ᶠ[𝓝 x] fun y ↦ g y + euclideanQuadratic K y := by
      filter_upwards [he] with y hy
      dsimp only [β] at hy
      linarith
    have hu1 := hug.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_add (hgx.differentiableAt two_ne_zero)
      (hq2.differentiable two_ne_zero x)] at hu1
    have hu2 := (hug.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    rw [second_fderiv_add_at hgx hq2.contDiffAt] at hu2
    constructor
    · rw [hu1]
      have hj' := hj.1.add (tendsto_const_nhds (x := fderiv ℝ (euclideanQuadratic K) x))
      convert hj' using 1
      funext j
      exact fderiv_fun_add ((hb2 j).differentiable two_ne_zero x)
        (hq2.differentiable two_ne_zero x)
    · rw [hu2]
      have hj' := hj.2.add
        (tendsto_const_nhds (x := fderiv ℝ (fderiv ℝ (euclideanQuadratic K)) x))
      convert hj' using 1
      funext j
      exact second_fderiv_add_at (hb2 j).contDiffAt hq2.contDiffAt

end PoincareConjecture.M10
