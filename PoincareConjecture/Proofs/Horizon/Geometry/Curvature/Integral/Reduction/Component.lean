import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import Mathlib.MeasureTheory.Integral.Bochner.Set










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem map_volumeMeasure_subtype_val {U : Opens M} (hclosed : IsClosed (U : Set M))
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w)) :
    gU.volumeMeasure.map Subtype.val = g.volumeMeasure.restrict U := by
  have hrange : Set.range (Subtype.val : U → M) = (U : Set M) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let mM : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨⟨gU.inner, gU.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let mU : EMetricSpace U := EMetricSpace.ofRiemannianMetric (𝓡 n) U
  have hi : @Isometry U M mU.toPseudoEMetricSpace mM.toPseudoEMetricSpace Subtype.val :=
    fun x y => (edist_subtype_val hclosed g gU hinner x y).symm
  have h := @Isometry.map_euclideanHausdorffMeasure U M mU _ _ mM _ _
    Subtype.val n hi
  change gU.volumeMeasure.map Subtype.val =
    g.volumeMeasure.restrict (Set.range (Subtype.val : U → M)) at h
  rw [hrange] at h
  exact h



theorem integral_ball_subtype_val {U : Opens M} (hclosed : IsClosed (U : Set M))
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (p : U) (r : ℝ) (h : M → ℝ) :
    (∫ x in gU.ball p r, h x ∂gU.volumeMeasure) =
      ∫ x in g.ball p r, h x ∂g.volumeMeasure := by
  have hpre : (Subtype.val : U → M) ⁻¹' g.ball p r = gU.ball p r := by
    ext x
    simp only [mem_preimage, ball, mem_ofPred_eq,
      edist_subtype_val hclosed g gU hinner]
  have hsub : g.ball p r ⊆ (U : Set M) := by
    intro x hx
    exact mem_of_edist_lt_top hclosed g p.property
      ((show g.edist p x < ENNReal.ofReal r from hx).trans_le le_top)
  have hi : MeasurableEmbedding (Subtype.val : U → M) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have he := hi.setIntegral_map (μ := gU.volumeMeasure) h (g.ball p r)
  rw [map_volumeMeasure_subtype_val hclosed g gU hinner, hpre] at he
  rw [Measure.restrict_restrict_of_subset hsub] at he
  exact he.symm



theorem integral_scalarCurvature_ball_subtype_val {U : Opens M}
    (hclosed : IsClosed (U : Set M))
    (g : RiemannianMetric n M) (gU : RiemannianMetric n U)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      gU.inner x v w = g.inner x
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w))
    (D : LeviCivitaData g) (DU : LeviCivitaData gU) (p : U) (r : ℝ) :
    (∫ x in gU.ball p r, DU.scalarCurvature x ∂gU.volumeMeasure) =
      ∫ x in g.ball p r, D.scalarCurvature x ∂g.volumeMeasure := by
  have hscalar : ∀ x : U, DU.scalarCurvature x = D.scalarCurvature x := by
    intro x
    apply DU.scalarCurvature_eq_of_local_isometry D isOpen_univ
      contMDiff_subtype_val.contMDiffOn (fun y _ v w => hinner y v w) (mem_univ x)
  simp_rw [hscalar]
  exact integral_ball_subtype_val hclosed g gU hinner p r D.scalarCurvature



theorem integral_scalarCurvature_ball_connectedComponent
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M) (r : ℝ) :
    let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    let gU := g.pullbackOfLocalDiffeomorph (Subtype.val : U → M)
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) U)
    (∫ x in gU.ball ⟨p, mem_connectedComponent⟩ r,
      gU.leviCivitaData.scalarCurvature x ∂gU.volumeMeasure) =
      ∫ x in g.ball p r, D.scalarCurvature x ∂g.volumeMeasure := by
  dsimp only
  exact integral_scalarCurvature_ball_subtype_val isClosed_connectedComponent g _
    (fun _ _ _ => rfl) D _ ⟨p, mem_connectedComponent⟩ r

end PoincareConjecture.RiemannianMetric
