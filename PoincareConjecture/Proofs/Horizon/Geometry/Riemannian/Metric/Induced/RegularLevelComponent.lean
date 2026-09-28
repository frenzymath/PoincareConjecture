import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

open Poincare.Geometry.Manifold.RegularLevel

variable {n : Nat} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {f : M -> Real} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(Real, Real) ∞ f)
  (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(Real, Real) f x ≠ 0)
  (c : Real)

private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩



theorem compactSpace_openRegularLevel
    (hcompact : IsCompact ((U : Set M) ∩ f ⁻¹' {c})) :
    CompactSpace (openLevelSet f U c) := by
  constructor
  apply (isEmbedding_openLevelIncl f U c).isCompact_iff.mpr
  rw [image_univ, range_openLevelIncl]
  exact hcompact


theorem compactSpace_regularLevelComponent
    (hcompact : IsCompact ((U : Set M) ∩ f ⁻¹' {c}))
    (p : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    CompactSpace (Poincare.connectedComponentOpens (EuclideanSpace Real (Fin n)) p) := by
  let := openLevelSetChartedSpace hf U hreg n c
  let : CompactSpace (openLevelSet f U c) := compactSpace_openRegularLevel U c hcompact
  exact isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact



theorem metricComplete_regularLevelComponentMetric [T3Space M]
    (g : RiemannianMetric (n + 1) M)
    (hcompact : IsCompact ((U : Set M) ∩ f ⁻¹' {c}))
    (p : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    MetricComplete ((regularLevelMetric hf U hreg c g).connectedComponentMetric p) := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  let : CompactSpace (openLevelSet f U c) := compactSpace_openRegularLevel U c hcompact
  have hcomplete : MetricComplete (regularLevelMetric hf U hreg c g) := by
    unfold MetricComplete
    infer_instance
  exact metricComplete_of_subtype_val isClosed_connectedComponent
    (regularLevelMetric hf U hreg c g) _ (fun _ _ _ => rfl) hcomplete




theorem sphere_regularLevelComponent_geometry
    {h : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Real}
    (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (U : Opens (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (hreg : ∀ x ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0)
    (c : Real) (hfull : h ⁻¹' {c} ⊆ (U : Set _))
    (p : openLevelSet h U c) :
    letI := openLevelSetChartedSpace hh U hreg 1 c
    letI := isManifold_openLevelSet hh U hreg 1 c
    let C := Poincare.connectedComponentOpens (EuclideanSpace Real (Fin 1)) p
    let gC := (regularLevelMetric hh U hreg c
      (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2)).connectedComponentMetric p
    IsManifold (𝓡 1) ∞ C ∧ CompactSpace C ∧ ConnectedSpace C ∧ MetricComplete gC := by
  let := openLevelSetChartedSpace hh U hreg 1 c
  let := isManifold_openLevelSet hh U hreg 1 c
  have hcompact : IsCompact ((U : Set _) ∩ h ⁻¹' {c}) := by
    rw [inter_eq_right.mpr hfull]
    exact (isClosed_singleton.preimage hh.continuous).isCompact
  exact ⟨inferInstance, compactSpace_regularLevelComponent hh U hreg c hcompact p,
    inferInstance, metricComplete_regularLevelComponentMetric hh U hreg c
      (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2) hcompact p⟩

end PoincareConjecture.RiemannianMetric
