import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.MetricPullbackForm
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension

/-!
# Continuity of the actual planar C1 pullback form

The tangent-bundle coordinate calculation retains only the regularity
needed for continuous coefficients. Triviality of the planar source
tangent bundle gives an ordinary continuous bilinear-valued function.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Form" => Plane →L[ℝ] Plane →L[ℝ] ℝ

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual metric pullback has continuous bilinear coefficients at every C1 point of the
target map. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project
construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem scalarC1_pullback_continuousAt (g : RiemannianMetric n M) {f : Plane → M}
    {p : Plane} (hf : ContMDiffAt (𝓡 2) (𝓡 n) 1 f p) :
    ContinuousAt (show Plane → Form from fun x => M60.metricPullbackForm (n := 2) g f x) p := by
  let T := TangentSpace (𝓡 2) (M := Plane)
  let E := EuclideanSpace ℝ (Fin n)
  let TM := TangentSpace (𝓡 n) (M := M)
  have hs : ContMDiffAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, Plane →L[ℝ] Plane →L[ℝ] ℝ)) 0
      (fun x => TotalSpace.mk' (Plane →L[ℝ] Plane →L[ℝ] ℝ) x
        (M60.metricPullbackForm (n := 2) g f x)) p := by
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    let A := inTangentCoordinates (𝓡 2) (𝓡 n) id f (mfderiv (𝓡 2) (𝓡 n) f) p
    let B := fun y => ContinuousLinearMap.inCoordinates E TM (E →L[ℝ] ℝ)
      (fun z => TM z →L[ℝ] ℝ) (f p) y (f p) y (g.inner y)
    have hA : ContMDiffAt (𝓡 2) 𝓘(ℝ, Plane →L[ℝ] E) 0 A p :=
      hf.mfderiv_const (by norm_num)
    have hB : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 0 B (f p) :=
      (((contMDiffAt_hom_bundle _).mp (g.contMDiff (f p))).2).of_le (by simp)
    have hform := (hA.clm_precomp (F₃ := ℝ)).clm_comp
      ((hB.comp p (hf.of_le (by norm_num))).clm_comp hA)
    apply hform.congr_of_eventuallyEq
    have hx := (trivializationAt Plane T p).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt Plane T p)
    have hy := hf.continuousAt.preimage_mem_nhds
      ((trivializationAt E TM (f p)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E TM (f p)))
    filter_upwards [hx, hy] with x hx hy
    exact M60.metricPullbackForm_coordinates g f hx hy
  rw [Bundle.contMDiffAt_section] at hs
  have hplain : ContMDiffAt (𝓡 2) 𝓘(ℝ, Plane →L[ℝ] Plane →L[ℝ] ℝ) 0
      (show Plane → Form from fun x => M60.metricPullbackForm (n := 2) g f x) p := by
    convert! hs using 1
    ext x v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]
  exact hplain.continuousAt

/-- A globally C1 target map has a globally continuous actual planar metric pullback.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project construction is
recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem scalarC1_pullback_continuous (g : RiemannianMetric n M) (f : Plane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    Continuous (show Plane → Form from fun x => M60.metricPullbackForm (n := 2) g f x) :=
  continuous_iff_continuousAt.mpr (fun _ => scalarC1_pullback_continuousAt g (hf _))

/-- A target map C1 on an open set has continuous actual pullback coefficients there.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project construction is
recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem scalarC1_pullback_continuousOn (g : RiemannianMetric n M) (f : Plane → M)
    {U : Set Plane} (hU : IsOpen U) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U) :
    ContinuousOn (show Plane → Form from fun x => M60.metricPullbackForm (n := 2) g f x) U :=
  fun _ hp => (scalarC1_pullback_continuousAt g
    (hf.contMDiffAt (hU.mem_nhds hp))).continuousWithinAt

end PoincareMT.M64Uniformization
