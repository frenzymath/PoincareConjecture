import PoincareConjecture.Proofs.M14.Mathlib.ChartFrame
import PoincareConjecture.Proofs.M14.Sec6_2_HorizontalTorsion
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCoordinates
import PoincareConjecture.Proofs.M12.Geometry.Manifold.ContDiff.LinearMap

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

noncomputable def horizontalChartFrame (x : G.Point) (v : SpacetimeModelVector n) :
    HorizontalSection G.spacetime :=
  fun p => G.spacetime.horizontalProjection p (VectorField.chartFrame (spacetimeModel n) x v p)

theorem horizontalChartFrame_smooth (x : G.Point) (v : SpacetimeModelVector n) :
    IsSmoothHorizontalSectionOn G.spacetime (horizontalChartFrame x v)
      (extChartAt (spacetimeModel n) x).source := by
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal) v.proj
          (G.spacetime.horizontalProjection v.proj v.2)) := G.spacetime.horizontalProjection_smooth
  simpa only [extChartAt_source, IsSmoothHorizontalSectionOn, horizontalChartFrame,
    Function.comp_def] using
    hproj.comp_contMDiffOn (VectorField.chartFrame_contMDiffOn (spacetimeModel n) x v)

variable (e : Trivialization (EuclideanSpace ℝ (Fin n))
    (TotalSpace.proj : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal → G.Point))
  [MemTrivializationAtlas e]

noncomputable def horizontalProjectionInCoordinates (x p : G.Point) :
    SpacetimeModelVector n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (e.continuousLinearMapAt ℝ p).comp ((G.spacetime.horizontalProjection p).comp
    ((trivializationAt (SpacetimeModelVector n)
      (TangentSpace (spacetimeModel n) : G.Point → Type _) x).symmL ℝ p))

theorem horizontalProjectionInCoordinates_contMDiffAt {x p : G.Point}
    (hx : p ∈ (extChartAt (spacetimeModel n) x).source) (he : p ∈ e.baseSet) :
    ContMDiffAt (spacetimeModel n)
      𝓘(ℝ, SpacetimeModelVector n →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (horizontalProjectionInCoordinates e x) p := by
  apply contMDiffAt_clm_of_apply_model
  intro v
  have hs := (horizontalChartFrame_smooth x v).contMDiffAt
    ((isOpen_extChartAt_source (I := spacetimeModel n) x).mem_nhds hx)
  have hc := (e.contMDiffAt_iff (f := fun q =>
    TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal) q
      (horizontalChartFrame x v q)) (e.mem_source.mpr he)).mp hs
  apply hc.2.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds he] with q hq
  exact e.continuousLinearMapAt_apply_of_mem ℝ hq _

theorem horizontalProjectionInCoordinates_curve_deriv
    {γ : ℝ → G.Point} {x : G.Point} {s : ℝ}
    (hx : γ s ∈ (extChartAt (spacetimeModel n) x).source)
    (hγ : MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) γ s) :
    horizontalProjectionInCoordinates e x (γ s)
        (deriv ((extChartAt (spacetimeModel n) x) ∘ γ) s) =
      e.continuousLinearMapAt ℝ (γ s) (G.spacetime.horizontalProjection (γ s)
        (mfderiv 𝓘(ℝ) (spacetimeModel n) γ s (1 : ℝ))) := by
  change e.continuousLinearMapAt ℝ (γ s) (G.spacetime.horizontalProjection (γ s)
    (VectorField.chartFrame (spacetimeModel n) x
      (deriv ((extChartAt (spacetimeModel n) x) ∘ γ) s) (γ s))) = _
  rw [VectorField.chartFrame_curve_deriv (spacetimeModel n)
    (by simpa only [extChartAt_source] using hx) hγ]

omit [MemTrivializationAtlas e] in

theorem horizontalChartFrame_covariant_symm
    (hCoordinates : M12MetricPredecessors.{0} n) {x p : G.Point}
    (hx : p ∈ (extChartAt (spacetimeModel n) x).source) (v w : SpacetimeModelVector n) :
    rawHorizontalCovariantDerivative G.leafwise (horizontalChartFrame x v) p
        (VectorField.chartFrame (spacetimeModel n) x w p) =
      rawHorizontalCovariantDerivative G.leafwise (horizontalChartFrame x w) p
        (VectorField.chartFrame (spacetimeModel n) x v p) := by
  have hframe (z : SpacetimeModelVector n) :
      ContMDiffOn (spacetimeModel n) (spacetimeModel n).tangent ∞
        (T% (VectorField.chartFrame (spacetimeModel n) x z))
        (extChartAt (spacetimeModel n) x).source := by
    simpa only [extChartAt_source] using
      VectorField.chartFrame_contMDiffOn (spacetimeModel n) x z
  have h := horizontalCovariantDerivative_projection_torsion hCoordinates G.leafwise
    G.gaugeCover (isOpen_extChartAt_source (I := spacetimeModel n) x) (hframe w) (hframe v) hx
  rw [VectorField.chartFrame_mlieBracket (spacetimeModel n)
    (by simpa only [extChartAt_source] using hx), map_zero] at h
  exact sub_eq_zero.mp h

theorem horizontalProjectionInCoordinates_torsion
    (hCoordinates : M12MetricPredecessors.{0} n) {x p : G.Point}
    (hx : p ∈ (extChartAt (spacetimeModel n) x).source) (he : p ∈ e.baseSet)
    (v w : SpacetimeModelVector n) :
    mvfderiv (spacetimeModel n) (fun q => horizontalProjectionInCoordinates e x q v) p
        (VectorField.chartFrame (spacetimeModel n) x w p) +
      e.continuousLinearMapAt ℝ p (horizontalConnectionDifference e p
        (horizontalChartFrame x v p) (VectorField.chartFrame (spacetimeModel n) x w p)) =
    mvfderiv (spacetimeModel n) (fun q => horizontalProjectionInCoordinates e x q w) p
        (VectorField.chartFrame (spacetimeModel n) x v p) +
      e.continuousLinearMapAt ℝ p (horizontalConnectionDifference e p
        (horizontalChartFrame x w p) (VectorField.chartFrame (spacetimeModel n) x v p)) := by
  have hdiff (z : SpacetimeModelVector n) :=
    ((horizontalChartFrame_smooth x z).contMDiffAt
      ((isOpen_extChartAt_source (I := spacetimeModel n) x).mem_nhds hx)).mdifferentiableAt
        (by simp)
  have hcoord (a b : SpacetimeModelVector n) :=
    e.covariantDerivative_eq_flat_add_difference
      ((rawHorizontalCovariantDerivative_isCovariantDerivative G.leafwise).mono
        (subset_univ e.baseSet)) he (hdiff a) (VectorField.chartFrame (spacetimeModel n) x b p)
  have h := congrArg (e.continuousLinearMapAt ℝ p)
    (horizontalChartFrame_covariant_symm hCoordinates hx v w)
  rw [hcoord v w, hcoord w v, map_add, map_add,
    e.continuousLinearMapAt_symmL he, e.continuousLinearMapAt_symmL he] at h
  exact h

end PoincareConjecture.M14
