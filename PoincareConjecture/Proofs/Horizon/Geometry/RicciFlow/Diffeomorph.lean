import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {J : Set ℝ}

noncomputable def pullbackDiffeomorph (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) : RicciFlow n M J :=
  F.pullbackWithConnection e e.isLocalDiffeomorph (fun t =>
    ((F.metric t).pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph).leviCivitaData)

@[simp] theorem pullbackDiffeomorph_inner (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
    ((F.pullbackDiffeomorph e).metric t).inner x v w =
      (F.metric t).inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) := rfl

theorem pullbackDiffeomorph_ricci (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
    ((F.pullbackDiffeomorph e).connection t).ricci x v w =
      (F.connection t).ricci (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) := by
  apply ((F.pullbackDiffeomorph e).connection t).ricci_eq_of_local_isometry
    (F.connection t) isOpen_univ e.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

@[simp] theorem pullbackDiffeomorph_scalarCurvature (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (x : M) :
    ((F.pullbackDiffeomorph e).connection t).scalarCurvature x =
      (F.connection t).scalarCurvature (e x) := by
  apply ((F.pullbackDiffeomorph e).connection t).scalarCurvature_eq_of_local_isometry
    (F.connection t) isOpen_univ e.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

@[simp] theorem pullbackDiffeomorph_curvatureTensorNorm (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (x : M) :
    ((F.pullbackDiffeomorph e).connection t).curvatureTensorNorm x =
      (F.connection t).curvatureTensorNorm (e x) := by
  apply ((F.pullbackDiffeomorph e).connection t).curvatureTensorNorm_eq_of_local_isometry
    (F.connection t) isOpen_univ e.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

@[simp] theorem pullbackDiffeomorph_curvatureDerivativeNorm (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (k : ℕ) (x : M) :
    ((F.pullbackDiffeomorph e).connection t).curvatureDerivativeNorm k x =
      (F.connection t).curvatureDerivativeNorm k (e x) := by
  apply ((F.pullbackDiffeomorph e).connection t).curvatureDerivativeNorm_eq_pullback
    (F.connection t) isOpen_univ e.contMDiff.contMDiffOn
    (fun y _ => ⟨e.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩)
    (fun _ _ _ _ => rfl) k (mem_univ x)

theorem pullbackDiffeomorph_nonnegativeCurvatureOperator_iff (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (x : M) :
    ((F.pullbackDiffeomorph e).connection t).NonnegativeCurvatureOperator x ↔
      (F.connection t).NonnegativeCurvatureOperator (e x) := by
  apply ((F.pullbackDiffeomorph e).connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
    (F.connection t) isOpen_univ e.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

@[simp] theorem pullbackDiffeomorph_edist (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (x y : M) :
    ((F.pullbackDiffeomorph e).metric t).edist x y =
      (F.metric t).edist (e x) (e y) :=
  RiemannianMetric.edist_diffeomorph _ _ e (fun _ _ _ => rfl) x y

theorem pullbackDiffeomorph_image_ball (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (x : M) (r : ℝ) :
    e '' ((F.pullbackDiffeomorph e).metric t).ball x r =
      (F.metric t).ball (e x) r :=
  RiemannianMetric.image_ball_diffeomorph _ _ e (fun _ _ _ => rfl) x r

@[simp] theorem pullbackDiffeomorph_metricComplete_iff [T3Space M] [T3Space N]
    (F : RicciFlow n N J) (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) :
    MetricComplete ((F.pullbackDiffeomorph e).metric t) ↔
      MetricComplete (F.metric t) :=
  RiemannianMetric.metricComplete_iff_diffeomorph _ _ e (fun _ _ _ => rfl)

@[simp] theorem pullbackDiffeomorph_volumeMeasure_ball [T3Space M] [T3Space N]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
    (F : RicciFlow n N J) (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (x : M) (r : ℝ) :
    ((F.pullbackDiffeomorph e).metric t).volumeMeasure
        (((F.pullbackDiffeomorph e).metric t).ball x r) =
      (F.metric t).volumeMeasure ((F.metric t).ball (e x) r) :=
  RiemannianMetric.volumeMeasure_ball_diffeomorph _ _ e (fun _ _ _ => rfl) x r

theorem pullbackDiffeomorph_scalarCurvature_mvfderiv
    (hC : RicciFlowCurvatureTheory.{v}) (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t : ℝ) (x : M) (w : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => ((F.pullbackDiffeomorph e).connection t).scalarCurvature y)
        x w =
      mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y) (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x w) := by
  have hid : (fun y => ((F.pullbackDiffeomorph e).connection t).scalarCurvature y) =
      (F.connection t).scalarCurvature ∘ e := by
    funext y
    exact F.pullbackDiffeomorph_scalarCurvature e t y
  rw [hid]
  exact mvfderiv_comp_apply x
    ((hC.tensor_calculus n N (F.metric t) (F.connection t)).contMDiff_scalarCurvature
      |>.mdifferentiable (by simp) (e x))
    (e.contMDiff.mdifferentiable (by simp) x) w

theorem finite_harnack_pullbackDiffeomorph
    (hC : RicciFlowCurvatureTheory.{v}) (F : RicciFlow n N J)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (t T₀ dR : ℝ) (x : M)
    (w : TangentSpace (𝓡 n) x) :
    (HasDerivWithinAt (fun s => ((F.pullbackDiffeomorph e).connection s).scalarCurvature x)
        dR J t ∧
      0 ≤ dR + ((F.pullbackDiffeomorph e).connection t).scalarCurvature x / (t - T₀) +
        2 * mvfderiv (𝓡 n)
          (fun y => ((F.pullbackDiffeomorph e).connection t).scalarCurvature y) x w +
        2 * ((F.pullbackDiffeomorph e).connection t).ricci x w w) ↔
    (HasDerivWithinAt (fun s => (F.connection s).scalarCurvature (e x)) dR J t ∧
      0 ≤ dR + (F.connection t).scalarCurvature (e x) / (t - T₀) +
        2 * mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y) (e x)
          (mfderiv (𝓡 n) (𝓡 n) e x w) +
        2 * (F.connection t).ricci (e x)
          (mfderiv (𝓡 n) (𝓡 n) e x w) (mfderiv (𝓡 n) (𝓡 n) e x w)) := by
  rw [F.pullbackDiffeomorph_scalarCurvature_mvfderiv hC]
  simp only [F.pullbackDiffeomorph_scalarCurvature, F.pullbackDiffeomorph_ricci]

end PoincareConjecture.RicciFlow
