import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.CylinderChart
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Charts.PartialHomeomorphCompact
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.Transport.GuardedCylinders
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Volume.LocalVolume
import PoincareLib.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison

/-!
# The actual cylinder image supplies the seed volume

Morgan--Tian Claim 16.27, p. 393. The inverse of the actual cylinder
slice chart has tangent norm at most two under the quadratic comparison.
Its volume distortion is therefore at most eight. A compact source
buffer remains inside the actual regular slice at an interior time.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M15
export PoincareMT.Generalized.Noncollapse (calibratedMetricVolume_eq_volumeMeasure)
end PoincareMT.M15

namespace PoincareMT.Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- The inverse chart has norm at most two under the actual lower
quadratic bound. Both derivatives are the supplied cylinder maps. -/
theorem cylinder_inverse_tangentNorm_le_two
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (g : RiemannianMetric 3 C.carrier) (s : ℝ) (hs : s ∈ I)
    (hmetric : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ 2 * (F.metric (origin + s / scale)).inner (e.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v))
    {y : (F.slice (origin + s / scale)).carrier} (hy : y ∈ e.forward s hs '' U)
    (v : TangentSpace (𝓡 3) y) :
    g.tangentNorm (e.inverse s hs y) (mfderiv (𝓡 3) (𝓡 3) (e.inverse s hs) y v) ≤
      2 * (F.metric (origin + s / scale)).tangentNorm y v := by
  let chart := M44.cylinderSliceChart e hU s hs
  have he : chart.toOpenPartialHomeomorph.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨chart.mdifferentiableOn (by simp), chart.symm.mdifferentiableOn (by simp)⟩
  have hd : (mfderiv (𝓡 3) (𝓡 3) chart (chart.symm y)).comp
      (mfderiv (𝓡 3) (𝓡 3) chart.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) y) := he.comp_symm_deriv hy
  have hv : mfderiv (𝓡 3) (𝓡 3) chart (chart.symm y)
      (mfderiv (𝓡 3) (𝓡 3) chart.symm y v) = v := congrArg (fun A => A v) hd
  have hm := hmetric (chart.symm y) (chart.map_target hy)
    (mfderiv (𝓡 3) (𝓡 3) chart.symm y v)
  change g.inner (chart.symm y) (mfderiv (𝓡 3) (𝓡 3) chart.symm y v)
      (mfderiv (𝓡 3) (𝓡 3) chart.symm y v) ≤
    2 * (F.metric (origin + s / scale)).inner (chart (chart.symm y))
      (mfderiv (𝓡 3) (𝓡 3) chart (chart.symm y)
        (mfderiv (𝓡 3) (𝓡 3) chart.symm y v))
      (mfderiv (𝓡 3) (𝓡 3) chart (chart.symm y)
        (mfderiv (𝓡 3) (𝓡 3) chart.symm y v)) at hm
  rw [hv] at hm
  have hright : chart.toPartialEquiv (chart.symm.toPartialEquiv y) = y := chart.right_inv hy
  have hinner := congrArg (fun q => (F.metric (origin + s / scale)).inner q v v) hright
  rw [hinner] at hm
  change g.inner (e.inverse s hs y) (mfderiv (𝓡 3) (𝓡 3) (e.inverse s hs) y v)
      (mfderiv (𝓡 3) (𝓡 3) (e.inverse s hs) y v) ≤
    2 * (F.metric (origin + s / scale)).inner y v v at hm
  have hn : 0 ≤ (F.metric (origin + s / scale)).inner y v v := by
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact ((F.metric (origin + s / scale)).pos y v hv0).le
  dsimp only [RiemannianMetric.tangentNorm]
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [Real.sq_sqrt hn]

/-- Every open seed subset has at most eight times its earlier image
volume in the actual metric calibration. -/
theorem cylinder_image_volume_ge_eighth
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (g : RiemannianMetric 3 C.carrier) (s : ℝ) (hs : s ∈ I)
    (hmetric : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ 2 * (F.metric (origin + s / scale)).inner (e.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v))
    {V : Set C.carrier} (hV : IsOpen V) (hVU : V ⊆ U) :
    calibratedMetricVolume g V ≤
      8 * calibratedMetricVolume (F.metric (origin + s / scale)) (e.forward s hs '' V) := by
  let chart := M44.cylinderSliceChart e hU s hs
  have hA : IsOpen (chart '' V) :=
    chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV hVU
  have himage : chart.symm '' (chart '' V) = V := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hleft : chart.symm.toPartialEquiv (chart.toPartialEquiv y) = y :=
        chart.left_inv (hVU hy)
      exact hleft.symm ▸ hy
    · intro hx
      exact ⟨chart x, mem_image_of_mem _ hx, chart.left_inv (hVU hx)⟩
  have hvol := (F.metric (origin + s / scale)).volumeMeasure_image_le_of_tangentNorm_le
    g chart.symm.toOpenPartialHomeomorph chart.open_target (Subset.refl _)
    (chart.symm.contMDiffOn.of_le (by simp)) (by norm_num : (0 : ℝ) < 2)
    (fun y hy v => cylinder_inverse_tangentNorm_le_two e hU g s hs hmetric hy v)
    hA.measurableSet (image_mono hVU)
  change g.volumeMeasure (chart.symm '' (chart '' V)) ≤
    ENNReal.ofReal 2 ^ 3 * (F.metric (origin + s / scale)).volumeMeasure (chart '' V) at hvol
  rw [himage] at hvol
  change g.volumeMeasure V ≤ ENNReal.ofReal 2 ^ 3 *
    (F.metric (origin + s / scale)).volumeMeasure (e.forward s hs '' V) at hvol
  simpa only [M15.calibratedMetricVolume_eq_volumeMeasure, ENNReal.ofReal_ofNat,
    show (2 : ℝ≥0∞) ^ (3 : ℕ) = 8 by norm_num] using hvol

/-- The image of a compact buffered seed is open, has compact closure,
and that entire closure lies in the actual retained regular region. -/
theorem cylinder_image_regular_compact_buffer
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ I) (hearlier : ∃ r ∈ I, r < s)
    {V : Set C.carrier} (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (hbuffer : closure V ⊆ U) :
    IsOpen (e.forward s hs '' V) ∧ IsCompact (closure (e.forward s hs '' V)) ∧
      closure (e.forward s hs '' V) ⊆ m33RegularRegion F (origin + s / scale) := by
  let chart := M44.cylinderSliceChart e hU s hs
  have hclosure := chart.toOpenPartialHomeomorph.image_closure_of_compact_buffer
    hcompact hbuffer
  change e.forward s hs '' closure V = closure (e.forward s hs '' V) at hclosure
  have hclosed : IsCompact (chart '' closure V) :=
    hcompact.image_of_continuousOn (chart.contMDiffOn.continuousOn.mono hbuffer)
  change IsCompact (e.forward s hs '' closure V) at hclosed
  have hregular := e.regular_image_of_earlier hs hearlier
  refine ⟨chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV
    (subset_closure.trans hbuffer), ?_, ?_⟩
  · exact hclosure ▸ hclosed
  · rw [← hclosure]
    exact (image_mono hbuffer).trans hregular

end PoincareMT.Proofs.M46
