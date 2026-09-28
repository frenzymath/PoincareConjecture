import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Instances.Real









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold Topology

universe u

namespace PoincareConjecture.M60



theorem plane_map_eq_of_mfderiv_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) 1 M]
    {f : E → M} (hf : MDifferentiable 𝓘(ℝ, E) (𝓡 n) f)
    (hzero : ∀ x, mfderiv 𝓘(ℝ, E) (𝓡 n) f x = 0) (x y : E) : f x = f y := by
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    let c := extChartAt (𝓡 n) (f p)
    have hO : IsOpen (f ⁻¹' c.source) := hf.continuous.isOpen_preimage _
      (isOpen_extChartAt_source (f p))
    have hp : p ∈ f ⁻¹' c.source := mem_extChartAt_source _
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hp)
    have hdc (q : E) (hq : q ∈ Metric.ball p r) :
        MDifferentiableAt (𝓡 n) (𝓡 n) c (f q) := by
      have hs : ContMDiffAt (𝓡 n) (𝓡 n) 1 c (f q) :=
        contMDiffAt_extChartAt' (x := f p) (n := 1) (by
          simpa only [c, Set.mem_preimage, extChartAt_source] using hsub hq)
      exact hs.mdifferentiableAt (by simp)
    have hd (q : E) (hq : q ∈ Metric.ball p r) :
        DifferentiableAt ℝ (c ∘ f) q := ((hdc q hq).comp q (hf q)).differentiableAt
    have hz (q : E) (hq : q ∈ Metric.ball p r) : fderiv ℝ (c ∘ f) q = 0 := by
      rw [← mfderiv_eq_fderiv, mfderiv_comp q (hdc q hq) (hf q), hzero]
      ext w
      change mfderiv (𝓡 n) (𝓡 n) c (f q) 0 = 0
      exact map_zero _
    filter_upwards [Metric.ball_mem_nhds p hr] with q hq
    have heq := (convex_ball p r).is_const_of_fderivWithin_eq_zero
      (fun z hz => (hd z hz).differentiableWithinAt)
      (fun z hzball => by
        rw [fderivWithin_of_isOpen Metric.isOpen_ball hzball]
        exact hz z hzball) hq (Metric.mem_ball_self hr)
    exact c.injOn (hsub hq) hp heq
  exact hlc.apply_eq_of_preconnectedSpace x y

end PoincareConjecture.M60
