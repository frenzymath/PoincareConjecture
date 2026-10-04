import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Derivatives of relative locally uniform limits

On a convex domain, locally uniform convergence of specified derivatives
and pointwise convergence of functions preserve the derivative within
the domain, including boundary points. This is the endpoint analytic step
for Morgan--Tian Proposition 5.14, pp. 90-91, and Claim 10.11, p. 255;
see task derivation 09.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

/-- Locally uniform derivative limits on a convex set identify the actual
within derivative at every point where the limiting derivative is continuous.
This includes the one-sided endpoints in task derivation 09. -/
theorem hasFDerivWithinAt_of_tendstoLocallyUniformlyOn_convex
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} [NeBot l] {S : Set E} (hS : Convex ℝ S)
    {f : ι → E → F} {f' : ι → E → E →L[ℝ] F}
    {g : E → F} {g' : E → E →L[ℝ] F}
    (hf : ∀ i x, x ∈ S → HasFDerivWithinAt (f i) (f' i x) S x)
    (hfg : ∀ x ∈ S, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hf' : TendstoLocallyUniformlyOn f' g' l S)
    {x : E} (hx : x ∈ S) (hg' : ContinuousWithinAt g' S x) :
    HasFDerivWithinAt g (g' x) S x := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨T, hT, huniform⟩ :=
    Metric.tendstoLocallyUniformlyOn_iff.mp hf' (ε / 2) (half_pos hε) x hx
  have hcont : {y | dist (g' y) (g' x) < ε / 2} ∈ 𝓝[S] x :=
    hg'.eventually (ball_mem_nhds _ (half_pos hε))
  obtain ⟨δ, hδ, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp (inter_mem hT hcont)
  apply Metric.mem_nhdsWithin_iff.mpr
  refine ⟨δ, hδ, fun y hy => ?_⟩
  apply le_of_tendsto (((hfg y hy.2).sub (hfg x hx)).sub_const (g' x (y - x))).norm
  filter_upwards [huniform] with i hi
  have hbound : ∀ z ∈ ball x δ ∩ S, ‖f' i z - g' x‖ ≤ ε := by
    intro z hz
    have hnear : dist (g' z) (g' x) < ε / 2 := (hlocal hz).2
    have happrox := hi z (hlocal hz).1
    have htriangle := dist_triangle (f' i z) (g' z) (g' x)
    simp only [dist_eq_norm] at htriangle
    rw [dist_eq_norm] at hnear
    rw [dist_eq_norm, norm_sub_rev] at happrox
    linarith
  have hmean := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => ((hf i z hz.2).mono inter_subset_right).sub
      (g' x).hasFDerivAt.hasFDerivWithinAt)
    hbound ((convex_ball x δ).inter hS) ⟨mem_ball_self hδ, hx⟩ hy
  simpa only [Pi.sub_apply, map_sub, sub_sub_sub_comm] using hmean
