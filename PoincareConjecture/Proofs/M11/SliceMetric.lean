import PoincareConjecture.Proofs.M11.SliceHorizontalMap
import PoincareConjecture.Proofs.M11.BilinearBundleSmooth
import PoincareConjecture.Proofs.M11.SpacetimeGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def sliceMetricForm (A : AdaptedMetricAtlas n X) (t : ℝ)
    (p : spacetimeSlice A.time t) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (adaptedHorizontalMetric A p.val).bilinearComp
    (sliceHorizontalEquiv A t p).toContinuousLinearMap
    (sliceHorizontalEquiv A t p).toContinuousLinearMap

theorem sliceMetricForm_pos (A : AdaptedMetricAtlas n X) (t : ℝ)
    (p : spacetimeSlice A.time t) (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < sliceMetricForm A t p v v := by
  apply adaptedHorizontalMetric_pos A p.val
  exact fun h ↦ hv ((sliceHorizontalEquiv A t p).injective (h.trans (map_zero _).symm))

theorem sliceMetricForm_smooth (A : AdaptedMetricAtlas n X) (t : ℝ) :
    letI := adaptedSliceChartedSpace A t
    letI : IsManifold (𝓡 n) ∞ (spacetimeSlice A.time t) := adaptedSlice_isManifold A t
    ContMDiff (𝓡 n)
      ((𝓡 n).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun p : spacetimeSlice A.time t ↦
          TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ)
        p (sliceMetricForm A t p)) := by
  let := adaptedChartedSpace A
  let : IsManifold (spacetimeModel n) ∞ X := adapted_isManifold A
  let := adaptedSliceChartedSpace A t
  let : IsManifold (𝓡 n) ∞ (spacetimeSlice A.time t) := adaptedSlice_isManifold A t
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  let := adaptedHorizontalVectorBundle A
  let := adaptedHorizontalSmoothBundle A
  intro p
  rw [← contMDiffWithinAt_univ]
  apply contMDiffWithinAt_bilinear_of_eval (IB := 𝓡 n) (J := 𝓡 n)
    (F := EuclideanSpace ℝ (Fin n))
    (E := (TangentSpace (𝓡 n) : spacetimeSlice A.time t → Type _))
    (b := id) (g := sliceMetricForm A t) contMDiffWithinAt_id
  intro v w
  have hg := (adaptedHorizontalMetric_smooth A).contMDiffAt.comp p
    (slice_inclusion_smooth A t p)
  have hv := (sliceHorizontalTangentMap_smooth A t).contMDiffAt.comp p
    (frameVector_contMDiffAt (IB := 𝓡 n)
      (E := (TangentSpace (𝓡 n) : spacetimeSlice A.time t → Type _)) p v)
  have hw := (sliceHorizontalTangentMap_smooth A t).contMDiffAt.comp p
    (frameVector_contMDiffAt (IB := 𝓡 n)
      (E := (TangentSpace (𝓡 n) : spacetimeSlice A.time t → Type _)) p w)
  have h := ContMDiffAt.clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : X ↦ ℝ)
    (b := (Subtype.val : spacetimeSlice A.time t → X))
    (ψ := fun x ↦ adaptedHorizontalMetric A x.val) hg hv hw
  exact (contMDiffAt_totalSpace.mp h).2.contMDiffWithinAt

noncomputable def adaptedSliceMetric (A : AdaptedMetricAtlas n X) (t : ℝ) :
    letI := adaptedSliceChartedSpace A t
    letI : IsManifold (𝓡 n) ∞ (spacetimeSlice A.time t) := adaptedSlice_isManifold A t
    RiemannianMetric n (spacetimeSlice A.time t) :=
  letI := adaptedSliceChartedSpace A t
  letI : IsManifold (𝓡 n) ∞ (spacetimeSlice A.time t) := adaptedSlice_isManifold A t
  {
    inner := sliceMetricForm A t
    symm := fun p v w ↦ adaptedHorizontalMetric_symm A p.val
      (sliceHorizontalEquiv A t p v) (sliceHorizontalEquiv A t p w)
    pos := sliceMetricForm_pos A t
    isVonNBounded := fun p ↦ positiveForm_isVonNBounded (sliceMetricForm A t p)
      (sliceMetricForm_pos A t p)
    contMDiff := sliceMetricForm_smooth A t
  }

end PoincareConjecture.Proofs.M11
