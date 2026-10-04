import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Pullback.OpenSurfaceClock
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.MovingMetric
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual density and weighted momentum derivatives on a surface

Morgan-Tian Lemma 6.4 and Definition 6.7, pp. 107-108. Parameter
differentiation has zero clock defect, while the weighted time-pair
derivative retains the actual +2 Ricci defect and sqrt derivative.
-/

set_option autoImplicit false
-- Both slice derivatives use the frozen scalar and horizontal tangent fibers.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {α : ℝ × ℝ → G.Point} {J P : Set ℝ} {T s v : ℝ}

/-- The actual original-time density has its geometric variation
derivative with no parameter-clock defect, Lemma 6.4, pp. 107-108. -/
theorem hasDerivAt_surfaceRawDensity (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P))
    (hclock : ∀ z ∈ J ×ˢ P, G.spacetime.timeFunction (α z) = T - z.1)
    (hs : s ∈ J) (hv : v ∈ P)
    (E : M14PullbackExtension G (fun u => α (s, u)) P (fun u => surfaceHorizontalFst α s u)) :
    HasDerivAt
      (fun u => M14RawLIntegrand G (fun r => α (r, u)) (fun r => surfaceHorizontalFst α r u) s)
      (Real.sqrt s *
        (M14HorizontalScalarDifferential G (α (s, v)) (surfaceHorizontalSnd α s v).val +
        2 * G.spacetime.horizontalMetric.inner (α (s, v)) (surfaceHorizontalFst α s v)
          (M14HorizontalCovariantDerivative G (fun u => α (s, u)) P
            (fun u => surfaceHorizontalFst α s u) E v))) v := by
  have hγ := (((hα _ ⟨hs, hv⟩).contMDiffAt ((hJ.prod hP).mem_nhds ⟨hs, hv⟩)).mdifferentiableAt
    (by simp)).comp v (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hscalar := ((H.scalar_smooth.mdifferentiable (by simp) (α (s, v))).hasMFDerivAt.comp v
    hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun u => horizontalScalarCurvature G.leafwise (α (s, u)))
    (M14HorizontalScalarDifferential G (α (s, v))
      (mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => α (s, u)) v 1)) v at hscalar
  rw [← surfaceHorizontalSnd_val hJ hP hα hclock hs hv] at hscalar
  have hmetric := horizontalCovariantDerivative_metric_product E E hv
    (hP.uniqueDiffOn v hv) hγ.mdifferentiableWithinAt
  rw [mfderivWithin_of_mem_nhds (hP.mem_nhds hv),
    surface_parameter_clock hJ hP hα hclock hs hv, mul_zero, zero_mul, sub_zero,
    G.spacetime.horizontalMetric.symm (α (s, v))
      (M14HorizontalCovariantDerivative G (fun u => α (s, u)) P
        (fun u => surfaceHorizontalFst α s u) E v)] at hmetric
  have hd := (hscalar.add (hmetric.hasDerivAt (hP.mem_nhds hv))).const_mul (Real.sqrt s)
  convert hd using 1 <;> first | rfl | ring

/-- The actual weighted momentum pairing has the sqrt derivative and
the +2 Ricci metric defect at positive backward time, Lemma 6.4 and
Definition 6.7, pp. 107-108. -/
theorem hasDerivAt_surfaceWeightedPair (hJ : IsOpen J) (hP : IsOpen P)
    (hα : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ α (J ×ˢ P))
    (hclock : ∀ z ∈ J ×ˢ P, G.spacetime.timeFunction (α z) = T - z.1)
    (hs : s ∈ J) (hv : v ∈ P) (hspos : 0 < s)
    (E : M14PullbackExtension G (fun r => α (r, v)) J (fun r => surfaceHorizontalFst α r v))
    (F : M14PullbackExtension G (fun r => α (r, v)) J (fun r => surfaceHorizontalSnd α r v)) :
    HasDerivAt
      (fun r => 2 * Real.sqrt r * G.spacetime.horizontalMetric.inner (α (r, v))
        (surfaceHorizontalFst α r v) (surfaceHorizontalSnd α r v))
      ((1 / Real.sqrt s) * G.spacetime.horizontalMetric.inner (α (s, v))
          (surfaceHorizontalFst α s v) (surfaceHorizontalSnd α s v) +
        2 * Real.sqrt s *
          (G.spacetime.horizontalMetric.inner (α (s, v))
              (M14HorizontalCovariantDerivative G (fun r => α (r, v)) J
                (fun r => surfaceHorizontalFst α r v) E s) (surfaceHorizontalSnd α s v) +
            G.spacetime.horizontalMetric.inner (α (s, v)) (surfaceHorizontalFst α s v)
              (M14HorizontalCovariantDerivative G (fun r => α (r, v)) J
                (fun r => surfaceHorizontalSnd α r v) F s) +
            2 * horizontalRicci G.leafwise (α (s, v))
              (surfaceHorizontalFst α s v) (surfaceHorizontalSnd α s v))) s := by
  have hγ := (((hα _ ⟨hs, hv⟩).contMDiffAt ((hJ.prod hP).mem_nhds ⟨hs, hv⟩)).mdifferentiableAt
    (by simp)).comp s (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hmetric := horizontalCovariantDerivative_metric_product E F hs
    (hJ.uniqueDiffOn s hs) hγ.mdifferentiableWithinAt
  rw [mfderivWithin_of_mem_nhds (hJ.mem_nhds hs), surface_time_clock hJ hP hα hclock hs hv]
    at hmetric
  have hweight : HasDerivAt (fun r : ℝ => 2 * Real.sqrt r) (1 / Real.sqrt s) s := by
    convert (Real.hasDerivAt_sqrt hspos.ne').const_mul 2 using 1 <;> first | rfl | ring
  convert hweight.mul (hmetric.hasDerivAt (hJ.mem_nhds hs)) using 1 <;> first | rfl | ring

end PoincareMT.M14
