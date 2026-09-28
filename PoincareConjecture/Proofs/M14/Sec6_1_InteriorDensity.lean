import PoincareConjecture.Proofs.M14.Sec6_2_CurveVelocity
import PoincareConjecture.Statements.M12GeneralizedEquation
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.SpecialFunctions.Sqrt










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {U : Set ℝ}



theorem projectedCurveVelocity_contMDiffOn_zero (hU : IsOpen U)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 0
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (γ s) (projectedCurveVelocity G γ s)) U := by
  have htan := hγ.contMDiffOn_mfderivWithin_const_apply hU.uniqueDiffOn (1 : ℝ)
    (k := 0) (by norm_num)
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  apply ((hproj.of_le (by simp : (0 : ℕ∞ω) ≤ ∞)).comp_contMDiffOn htan).congr
  intro s hs
  simp only [Function.comp_apply, projectedCurveVelocity,
    mfderivWithin_of_mem_nhds (hU.mem_nhds hs)]




theorem rawLIntegrand_projectedVelocity_continuousOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hU : IsOpen U)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ U) :
    ContinuousOn (M14RawLIntegrand G γ (projectedCurveVelocity G γ)) U := by
  have hv := projectedCurveVelocity_contMDiffOn_zero hU hγ
  have hmetricZero := G.spacetime.horizontalMetric.contMDiff.of_le (by simp : (0 : ℕ∞ω) ≤ ∞)
  have hmetric := hmetricZero.comp_contMDiffOn (hγ.of_le (by simp))
  have hpair := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial G.Point ℝ) hv hv
  have hkinetic : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 0
      (fun s => G.spacetime.horizontalMetric.inner (γ s)
        (projectedCurveVelocity G γ s) (projectedCurveVelocity G γ s)) U := by
    intro s hs
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
      using (Bundle.contMDiffWithinAt_totalSpace.mp (hpair s hs)).2
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  exact Real.continuous_sqrt.continuousOn.mul
    ((H.scalar_smooth.continuous.comp_continuousOn hγ.continuousOn).add hkinetic.continuousOn)




theorem backwardPath_velocity_eq_projected {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y) {s : ℝ} (hs : s ∈ Ioo τ₁ τ₂) :
    p.horizontal_velocity s = projectedCurveVelocity G p.curve s := by
  have hp := projectedCurveVelocity_derivative_eq (T := T)
    (((p.curve_regular s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt
      (by simp)) (show (fun r => G.spacetime.timeFunction (p.curve r)) =ᶠ[𝓝 s]
        (fun r => T - r) from by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact p.curve_time r (Ioo_subset_Icc_self hr))
  exact Subtype.ext (add_left_cancel ((p.derivative_eq s hs).symm.trans hp))

end PoincareConjecture.M14
