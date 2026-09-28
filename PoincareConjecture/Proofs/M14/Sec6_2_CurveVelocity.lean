import PoincareConjecture.Definitions.M14PathCalculus
import PoincareConjecture.Proofs.M14.Mathlib.WithinVelocitySmooth
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}


noncomputable def projectedCurveVelocity (G : GeneralizedLGeometryTransport n X time I)
    (γ : ℝ → G.Point) (s : ℝ) : G.Horizontal (γ s) :=
  G.spacetime.horizontalProjection (γ s)
    (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) γ s (1 : ℝ))



noncomputable def projectedCurveVelocityWithin (G : GeneralizedLGeometryTransport n X time I)
    (γ : ℝ → G.Point) (J : Set ℝ) (s : ℝ) : G.Horizontal (γ s) :=
  G.spacetime.horizontalProjection (γ s)
    (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))

variable {G : GeneralizedLGeometryTransport n X time I} {γ β : ℝ → G.Point} {J : Set ℝ}



theorem projectedCurveVelocityWithin_smooth (hJ : UniqueDiffOn ℝ J)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ γ J) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (γ s) (projectedCurveVelocityWithin G γ J s)) J := by
  have htan := hγ.contMDiffOn_mfderivWithin_const_apply hJ (1 : ℝ) (k := ∞) (by simp)
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  exact hproj.comp_contMDiffOn htan



theorem projectedCurveVelocity_derivative_eq {T s : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (spacetimeModel n) γ s)
    (hclock : (fun r => G.spacetime.timeFunction (γ r)) =ᶠ[𝓝 s] fun r => T - r) :
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) γ s (1 : ℝ) =
      -G.spacetime.timeVector (γ s) + (projectedCurveVelocity G γ s).val := by
  have ht : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have hd := ((ht.mdifferentiable (by simp) (γ s)).hasMFDerivAt.comp s
    hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hc : HasDerivAt (fun r => G.spacetime.timeFunction (γ r)) (-1) s := by
    simpa only [zero_sub] using
      ((hasDerivAt_const s T).sub (hasDerivAt_id s)).congr_of_eventuallyEq hclock
  have hv : (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s)
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) γ s (1 : ℝ))) = -1 := hd.unique hc
  unfold projectedCurveVelocity
  rw [G.spacetime.horizontalProjection_eq]
  change _ = -G.spacetime.timeVector (γ s) +
    (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) γ s (1 : ℝ) -
      (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s)
        (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) γ s (1 : ℝ))) •
          G.spacetime.timeVector (γ s))
  rw [hv, neg_smul, one_smul, sub_neg_eq_add]
  abel



theorem rawLIntegrand_projectedVelocity_congr {s : ℝ} (h : γ =ᶠ[𝓝 s] β) :
    M14RawLIntegrand G γ (projectedCurveVelocity G γ) s =
      M14RawLIntegrand G β (projectedCurveVelocity G β) s := by
  have hd := h.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
  unfold M14RawLIntegrand projectedCurveVelocity
  rw [hd, h.eq_of_nhds]

end PoincareConjecture.M14
