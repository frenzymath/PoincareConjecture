import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.ConnectedComponent

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

noncomputable def restrictToOpen (F : RicciFlow n M J) (U : Opens M) :
    RicciFlow n U J :=
  F.pullbackWithConnection Subtype.val (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) U)
    (fun t => ((F.metric t).pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) U)).leviCivitaData)

@[simp] theorem restrictToOpen_inner (F : RicciFlow n M J) (U : Opens M)
    (t : ℝ) (x : U) (v w : TangentSpace (𝓡 n) x) :
    ((F.restrictToOpen U).metric t).inner x v w = (F.metric t).inner x
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w) := rfl

noncomputable def restrictComponent (F : RicciFlow n M J) (p : M) :
    RicciFlow n (Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) J :=
  F.restrictToOpen (Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p)

@[simp] theorem restrictComponent_inner (F : RicciFlow n M J) (p : M)
    (t : ℝ) (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p)
    (v w : TangentSpace (𝓡 n) x) :
    ((F.restrictComponent p).metric t).inner x v w = (F.metric t).inner x
      (mfderiv (𝓡 n) (𝓡 n) Subtype.val x v)
      (mfderiv (𝓡 n) (𝓡 n) Subtype.val x w) := rfl

theorem restrictComponent_edist (F : RicciFlow n M J) (p : M) (t : ℝ)
    (x y : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) :
    ((F.restrictComponent p).metric t).edist x y = (F.metric t).edist x y :=
  RiemannianMetric.edist_subtype_val isClosed_connectedComponent
    (F.metric t) ((F.restrictComponent p).metric t) (fun _ _ _ => rfl) x y

theorem restrictComponent_metricComplete [T3Space M]
    (F : RicciFlow n M J) (p : M) (t : ℝ) (ht : MetricComplete (F.metric t)) :
    MetricComplete ((F.restrictComponent p).metric t) :=
  RiemannianMetric.metricComplete_of_subtype_val isClosed_connectedComponent
    (F.metric t) ((F.restrictComponent p).metric t) (fun _ _ _ => rfl) ht

theorem restrictComponent_volumeMeasure_ball [T3Space M]
    [MeasurableSpace M] [BorelSpace M] (F : RicciFlow n M J) (p : M) (t : ℝ)
    (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) (r : ℝ) :
    ((F.restrictComponent p).metric t).volumeMeasure
        (((F.restrictComponent p).metric t).ball x r) =
      (F.metric t).volumeMeasure ((F.metric t).ball x r) :=
  RiemannianMetric.volumeMeasure_ball_subtype_val isClosed_connectedComponent
    (F.metric t) ((F.restrictComponent p).metric t) (fun _ _ _ => rfl) x r

theorem restrictComponent_curvatureTensor (F : RicciFlow n M J) (p : M) (t : ℝ)
    (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p)
    (v w z a : TangentSpace (𝓡 n) x) :
    ((F.restrictComponent p).connection t).curvatureTensor x v w z a =
      (F.connection t).curvatureTensor x
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x v)
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x w)
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x z)
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x a) := by
  apply ((F.restrictComponent p).connection t).curvatureTensor_eq_of_local_isometry
    (F.connection t) isOpen_univ contMDiff_subtype_val.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem restrictComponent_scalarCurvature (F : RicciFlow n M J) (p : M) (t : ℝ)
    (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) :
    ((F.restrictComponent p).connection t).scalarCurvature x =
      (F.connection t).scalarCurvature x := by
  apply ((F.restrictComponent p).connection t).scalarCurvature_eq_of_local_isometry
    (F.connection t) isOpen_univ contMDiff_subtype_val.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem restrictComponent_curvatureTensorNorm (F : RicciFlow n M J) (p : M) (t : ℝ)
    (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) :
    ((F.restrictComponent p).connection t).curvatureTensorNorm x =
      (F.connection t).curvatureTensorNorm x := by
  apply ((F.restrictComponent p).connection t).curvatureTensorNorm_eq_of_local_isometry
    (F.connection t) isOpen_univ contMDiff_subtype_val.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem restrictComponent_nonnegativeCurvatureOperator_iff
    (F : RicciFlow n M J) (p : M) (t : ℝ)
    (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) :
    ((F.restrictComponent p).connection t).NonnegativeCurvatureOperator x ↔
      (F.connection t).NonnegativeCurvatureOperator x := by
  apply ((F.restrictComponent p).connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
    (F.connection t) isOpen_univ contMDiff_subtype_val.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem exists_restrictComponent
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    {J : Set ℝ} (F : RicciFlow n M J) (p : M) :
    let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    ∃ G : RicciFlow n U J,
      (∀ t (x : U) (v w : TangentSpace (𝓡 n) x),
        (G.metric t).inner x v w = (F.metric t).inner x
          (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
          (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w)) ∧
      (∀ t (x y : U), (G.metric t).edist x y = (F.metric t).edist x y) ∧
      (∀ t, MetricComplete (F.metric t) → MetricComplete (G.metric t)) ∧
      (∀ t (x : U) (r : ℝ),
        (G.metric t).volumeMeasure ((G.metric t).ball x r) =
          (F.metric t).volumeMeasure ((F.metric t).ball x r)) ∧
      (∀ t (x : U) (v w z a : TangentSpace (𝓡 n) x),
        (G.connection t).curvatureTensor x v w z a =
          (F.connection t).curvatureTensor x
            (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
            (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w)
            (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x z)
            (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x a)) ∧
      (∀ t (x : U), (G.connection t).scalarCurvature x =
        (F.connection t).scalarCurvature x) ∧
      (∀ t (x : U), (G.connection t).curvatureTensorNorm x =
        (F.connection t).curvatureTensorNorm x) ∧
      (∀ t (x : U), (G.connection t).NonnegativeCurvatureOperator x ↔
        (F.connection t).NonnegativeCurvatureOperator x) := by
  exact ⟨F.restrictComponent p, F.restrictComponent_inner p,
    F.restrictComponent_edist p, F.restrictComponent_metricComplete p,
    F.restrictComponent_volumeMeasure_ball p, F.restrictComponent_curvatureTensor p,
    F.restrictComponent_scalarCurvature p, F.restrictComponent_curvatureTensorNorm p,
    F.restrictComponent_nonnegativeCurvatureOperator_iff p⟩

end PoincareConjecture.RicciFlow
