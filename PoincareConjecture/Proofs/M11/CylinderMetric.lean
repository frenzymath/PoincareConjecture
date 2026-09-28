import PoincareConjecture.Proofs.M11.CylinderSpatialSmooth
import PoincareConjecture.Proofs.M11.BilinearBundleSmooth
import PoincareConjecture.Proofs.M11.PositiveFormBounded
import PoincareConjecture.Proofs.M11.IntervalFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {D : SmoothSpacetimeInterval K}
  {C : Type*} [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ C]

noncomputable def cylinderMetricForm (e : CompatibleSpacetimeCylinder F D C)
    (t : D.Point) (x : C) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := by
  let H : Submodule ℝ (SpacetimeModelVector n) :=
    spacetimeHorizontal F.timeFunction (e.toSpacetime (t, x))
  exact (show H →L[ℝ] H →L[ℝ] ℝ from
    F.horizontalMetric.inner (e.toSpacetime (t, x))).bilinearComp
      (show EuclideanSpace ℝ (Fin n) →L[ℝ] H from
        (cylinderSpatialEquiv e t x).toContinuousLinearMap)
      (show EuclideanSpace ℝ (Fin n) →L[ℝ] H from
        (cylinderSpatialEquiv e t x).toContinuousLinearMap)

theorem cylinderMetricForm_pos (e : CompatibleSpacetimeCylinder F D C)
    (t : D.Point) (x : C) (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < cylinderMetricForm e t x v v := by
  apply F.horizontalMetric.pos
  exact fun h ↦ hv ((cylinderSpatialEquiv e t x).injective (h.trans (map_zero _).symm))

theorem cylinderMetricForm_smooth (e : CompatibleSpacetimeCylinder F D C) :
    ContMDiff (spacetimeModel n)
      ((𝓡 n).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p : D.Point × C ↦ TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun x : C ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
        p.2 (cylinderMetricForm e p.1 p.2)) := by
  intro p
  rw [← contMDiffWithinAt_univ]
  apply contMDiffWithinAt_bilinear_of_eval (IB := 𝓡 n) (J := spacetimeModel n)
    (F := EuclideanSpace ℝ (Fin n)) (E := (TangentSpace (𝓡 n) : C → Type _))
    (b := Prod.snd) (g := fun p ↦ cylinderMetricForm e p.1 p.2) contMDiffWithinAt_snd
  intro v w
  have hg := F.horizontalMetric.contMDiff.contMDiffAt.comp p (e.smooth p)
  have hv := (cylinderSpatialTangentMap_smooth e).contMDiffAt.comp p
    (contMDiffAt_fst.prodMk
      ((frameVector_contMDiffAt (IB := 𝓡 n)
        (E := (TangentSpace (𝓡 n) : C → Type _)) p.2 v).comp p contMDiffAt_snd))
  have hw := (cylinderSpatialTangentMap_smooth e).contMDiffAt.comp p
    (contMDiffAt_fst.prodMk
      ((frameVector_contMDiffAt (IB := 𝓡 n)
        (E := (TangentSpace (𝓡 n) : C → Type _)) p.2 w).comp p contMDiffAt_snd))
  have h := ContMDiffAt.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : F.Point ↦ ℝ)
    (b := e.toSpacetime) (ψ := fun q ↦ F.horizontalMetric.inner (e.toSpacetime q)) hg hv hw
  exact (contMDiffAt_totalSpace.mp h).2.contMDiffWithinAt

noncomputable def cylinderMetricAt (e : CompatibleSpacetimeCylinder F D C)
    (t : D.Point) : RiemannianMetric n C where
  inner := cylinderMetricForm e t
  symm := fun x v w ↦ F.horizontalMetric.symm (e.toSpacetime (t, x))
    (cylinderSpatialEquiv e t x v) (cylinderSpatialEquiv e t x w)
  pos := cylinderMetricForm_pos e t
  isVonNBounded := fun x ↦ positiveForm_isVonNBounded (cylinderMetricForm e t x)
    (cylinderMetricForm_pos e t x)
  contMDiff := (cylinderMetricForm_smooth e).comp (contMDiff_const.prodMk contMDiff_id)

noncomputable def cylinderMetricTime (K : SpacetimeInterval) (t : ℝ) : K.domain := by
  classical
  exact if ht : t ∈ K.domain then ⟨t, ht⟩
    else ⟨K.nontrivial.nonempty.some, K.nontrivial.nonempty.some_mem⟩

theorem cylinderMetricTime_of_mem (K : SpacetimeInterval) (t : K.domain) :
    cylinderMetricTime K t.val = t := by
  simp [cylinderMetricTime, t.property]

noncomputable def pulledCylinderMetric
    (e : CompatibleSpacetimeCylinder F (smoothInterval K) C) : SpacetimeCylinderMetric e where
  metric := fun t ↦ cylinderMetricAt e (cylinderMetricTime K t)
  smooth := by
    apply interval_family_smoothOn K (cylinderMetricForm_smooth e)
    intro t x
    simp only [cylinderMetricTime_of_mem]
    rfl
  spatialTangentEquiv := cylinderSpatialEquiv e
  spatialTangentEquiv_eq := cylinderSpatialEquiv_eq e
  metric_eq := by
    intro t x v w
    change cylinderMetricForm e (cylinderMetricTime K t.val) x v w = _
    rw [cylinderMetricTime_of_mem]
    rfl

end PoincareConjecture.Proofs.M11
