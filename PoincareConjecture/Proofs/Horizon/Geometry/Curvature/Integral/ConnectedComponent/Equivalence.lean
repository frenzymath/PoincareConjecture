import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.ConnectedComponent.Similarity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Manifold ContDiff Bundle
namespace PoincareConjecture.RiemannianMetric
variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

theorem connectedComponentMetric_geometry_diffeomorph
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w))
    (p : M) :
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    let E := Poincare.connectedComponentDiffeomorph e p
    let gC := g.connectedComponentMetric p
    let hC := h.connectedComponentMetric (e p)
    (∀ (x : C) (v w : TangentSpace (𝓡 n) x),
      gC.inner x v w = hC.inner (E x) (mfderiv (𝓡 n) (𝓡 n) E x v)
        (mfderiv (𝓡 n) (𝓡 n) E x w)) ∧
    (∀ x y : C, hC.edist (E x) (E y) = gC.edist x y) ∧
    MeasurePreserving E gC.volumeMeasure hC.volumeMeasure ∧
    (∀ x : C, gC.leviCivitaData.scalarCurvature x =
      hC.leviCivitaData.scalarCurvature (E x)) ∧
    (∀ K : C → ℝ,
      (∫ x, K x ∂gC.volumeMeasure) = ∫ y, K (E.symm y) ∂hC.volumeMeasure) ∧
    ∀ Ψ : ℝ → ℝ,
      (∫ x, Ψ (gC.leviCivitaData.scalarCurvature x) ∂gC.volumeMeasure) =
        ∫ y, Ψ (hC.leviCivitaData.scalarCurvature y) ∂hC.volumeMeasure := by
  dsimp only
  let E := Poincare.connectedComponentDiffeomorph e p
  let gC := g.connectedComponentMetric p
  let hC := h.connectedComponentMetric (e p)
  have hm (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p)
      (v w : TangentSpace (𝓡 n) x) :
      gC.inner x v w = hC.inner (E x)
        (mfderiv (𝓡 n) (𝓡 n) E x v) (mfderiv (𝓡 n) (𝓡 n) E x w) := by
    simpa only [one_mul] using (g.connectedComponentMetric_inner_diffeomorph h e
      (a := 1) (fun x v w => by simpa only [one_mul] using (hinner x v w).symm)
      p x v w).symm
  have hd := gC.edist_eq_of_diffeomorph_metric_pullback hC E hm
  refine ⟨hm, hd, ?_, ?_, ?_, ?_⟩
  · exact gC.measurePreserving_volumeMeasure_of_edist_eq hC E.toEquiv hd
  · intro x
    exact gC.leviCivitaData.scalarCurvature_eq_of_local_isometry hC.leviCivitaData
      isOpen_univ E.contMDiff.contMDiffOn (fun x _ => hm x) (mem_univ x)
  · intro K
    have hint := gC.integral_comp_equiv_volumeMeasure hC E.toEquiv hd (K ∘ E.symm)
    change (∫ x, K (E.symm (E x)) ∂gC.volumeMeasure) =
      ∫ y, K (E.symm y) ∂hC.volumeMeasure at hint
    simpa only [Diffeomorph.symm_apply_apply] using hint
  · exact fun Ψ => gC.leviCivitaData.integral_scalarCurvature_eq_of_diffeomorph
      hC.leviCivitaData E hm Ψ

end PoincareConjecture.RiemannianMetric
