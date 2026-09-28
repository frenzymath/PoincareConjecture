import PoincareConjecture.Proofs.M14.Sec6_2_OpenSurfaceFields
import Mathlib.Analysis.Calculus.Deriv.Add









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {α : ℝ × ℝ → G.Point} {J P : Set ℝ} {T s v : ℝ}



theorem surface_time_clock (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P))
    (hclock : ∀ z ∈ J ×ˢ P, G.spacetime.timeFunction (α z) = T - z.1)
    (hs : s ∈ J) (hv : v ∈ P) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (α (s, v))
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r => α (r, v)) s (1 : ℝ))) = -1 := by
  have hγ := (((hα _ ⟨hs, hv⟩).contMDiffAt ((hJ.prod hP).mem_nhds ⟨hs, hv⟩)).mdifferentiableAt
    (by simp)).comp s (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have htime : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have hd := ((htime.mdifferentiable (by simp) (α (s, v))).hasMFDerivAt.comp s
    hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hc : HasDerivAt (fun r => G.spacetime.timeFunction (α (r, v))) (-1) s := by
    apply (show HasDerivAt (fun r : ℝ => T - r) (-1) s from by
      exact (hasDerivAt_id s).const_sub T).congr_of_eventuallyEq
    filter_upwards [hJ.mem_nhds hs] with r hr
    exact hclock (r, v) ⟨hr, hv⟩
  exact hd.unique hc



theorem surface_parameter_clock (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P))
    (hclock : ∀ z ∈ J ×ˢ P, G.spacetime.timeFunction (α z) = T - z.1)
    (hs : s ∈ J) (hv : v ∈ P) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (α (s, v))
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => α (s, u)) v (1 : ℝ))) = 0 := by
  have hγ := (((hα _ ⟨hs, hv⟩).contMDiffAt ((hJ.prod hP).mem_nhds ⟨hs, hv⟩)).mdifferentiableAt
    (by simp)).comp v (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have htime : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have hd := ((htime.mdifferentiable (by simp) (α (s, v))).hasMFDerivAt.comp v
    hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hc : HasDerivAt (fun u => G.spacetime.timeFunction (α (s, u))) 0 v := by
    apply (hasDerivAt_const v (T - s)).congr_of_eventuallyEq
    filter_upwards [hP.mem_nhds hv] with u hu
    exact hclock (s, u) ⟨hs, hu⟩
  exact hd.unique hc



theorem surfaceHorizontalSnd_val (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P))
    (hclock : ∀ z ∈ J ×ˢ P, G.spacetime.timeFunction (α z) = T - z.1)
    (hs : s ∈ J) (hv : v ∈ P) :
    (surfaceHorizontalSnd α s v).val =
      mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => α (s, u)) v (1 : ℝ) := by
  unfold surfaceHorizontalSnd
  rw [G.spacetime.horizontalProjection_eq]
  change mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => α (s, u)) v (1 : ℝ) -
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (α (s, v))
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => α (s, u)) v (1 : ℝ))) •
        G.spacetime.timeVector (α (s, v)) = _
  rw [surface_parameter_clock hJ hP hα hclock hs hv, zero_smul, sub_zero]

end PoincareConjecture.M14
