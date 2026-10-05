import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.Coordinates.TimeSliceHomeomorph
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Metric.Coordinates.MetricCoordinates
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Theory

/-!
# The actual regular L-exponential slice in fixed terminal coordinates

The source and target are the exact canonical regular slices. Smoothness
comes from the same time-preserving spacetime branch supplied by G.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
/-- The exact regular slice chart normalized by one fixed terminal orthonormal basis. -/
noncomputable def exponentialSliceChart (G : LExponentialGeometry F T τmax p) (τ : ℝ) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  exact
    ((metricCoordinates (F.metric T) p).toHomeomorph).transOpenPartialHomeomorph
    (timeSliceHomeomorph G.regular_chart
      (fun z ↦ congrArg Prod.snd (G.regular_forward z)) G.regular_inverse_time τ)

/-- The total forward map is the actual L-exponential family in the fixed coordinates. -/
theorem exponentialSliceChart_apply (G : LExponentialGeometry F T τmax p) (τ : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    exponentialSliceChart G τ z = G.gamma (metricCoordinates (F.metric T) p z) τ := by
  change (timeSliceHomeomorph G.regular_chart
      (fun z ↦ congrArg Prod.snd (G.regular_forward z)) G.regular_inverse_time τ)
      (metricCoordinates (F.metric T) p z) = _
  change (G.regular_chart (metricCoordinates (F.metric T) p z, τ)).1 = _
  rw [G.regular_forward]

/-- The exact source is the canonical regular initial-vector slice. -/
theorem exponentialSliceChart_source (G : LExponentialGeometry F T τmax p) (τ : ℝ) :
    (exponentialSliceChart G τ).source =
      {z | (metricCoordinates (F.metric T) p z, τ) ∈ G.toLExponentialFamily.regularDomain} := by
  simp [exponentialSliceChart, timeSliceHomeomorph, G.regular_source]

/-- The exact target is the regular spacetime image at the chosen time. -/
theorem exponentialSliceChart_target (G : LExponentialGeometry F T τmax p) (τ : ℝ) :
    (exponentialSliceChart G τ).target = {q | (q, τ) ∈ G.regularImage} := by
  change {q | (q, τ) ∈ G.regular_chart.target} = _
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The forward regular slice is smooth on its actual source. -/
theorem exponentialSliceChart_contMDiffOn (G : LExponentialGeometry F T τmax p) (τ : ℝ) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (exponentialSliceChart G τ)
      (exponentialSliceChart G τ).source := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := (metricCoordinates (F.metric T) p).toContinuousLinearEquiv
  have hs := timeSliceHomeomorph_contMDiffOn G.regular_chart
    (fun z ↦ congrArg Prod.snd (G.regular_forward z)) G.regular_inverse_time τ
    G.regular_forward_smooth
  have hcomp := hs.comp β.toContinuousLinearMap.contMDiff.contMDiffOn (fun _ hx ↦ hx)
  exact hcomp

set_option backward.isDefEq.respectTransparency false in
/-- The inverse regular slice is smooth on its actual target. -/
theorem exponentialSliceChart_symm_contMDiffOn (G : LExponentialGeometry F T τmax p) (τ : ℝ) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (exponentialSliceChart G τ).symm
      (exponentialSliceChart G τ).target := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := (metricCoordinates (F.metric T) p).toContinuousLinearEquiv
  have hs := timeSliceHomeomorph_symm_contMDiffOn G.regular_chart
    (fun z ↦ congrArg Prod.snd (G.regular_forward z)) G.regular_inverse_time τ
    G.regular_inverse_smooth
  have hcomp := β.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hs
  exact hcomp

end PoincareMT.ReducedVolume
