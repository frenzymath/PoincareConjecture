import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SurfaceLine
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.RicciFlow

theorem small_surface_curvature_eq_zero_of_minimizing_line
    {M : Type} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {J : Set ℝ} (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 2 M J)
    (t : ℝ) (hcomplete : MetricComplete (F.metric t))
    (hoperator : ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (γ : ℝ → M)
    (hγ : ∀ s r : ℝ, (F.metric t).edist (γ s) (γ r) = ENNReal.ofReal |s - r|) :
    (∀ x, (F.connection t).scalarCurvature x = 0) ∧
      ∀ x, (F.connection t).curvatureTensorNorm x = 0 := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (ULift.{u} M) :=
    Poincare.Manifold.uliftChartedSpace _ M
  let : IsManifold (𝓡 2) ∞ (ULift.{u} M) :=
    Poincare.Manifold.uliftIsManifold (𝓡 2) M
  let : ConnectedSpace (ULift.{u} M) :=
    (Homeomorph.ulift.connectedSpace_iff).mpr inferInstance
  let H : RicciFlow 2 (ULift.{u} M) J := F.ulift
  have hD := hC.tensor_calculus 2 (ULift.{u} M) (H.metric t) (H.connection t)
  have hRic : (H.connection t).NonnegativeRicciCurvature := by
    intro x v
    exact ((H.connection t).ricci_bounds_of_nonnegative_curvatureOperator hD x
      ((F.ulift_nonnegativeCurvatureOperator_iff t x).mpr (hoperator x.down)) v).1
  have hflat := (H.metric t).surface_curvature_eq_zero_of_minimizing_line
    (H.connection t) hD ((F.ulift_metricComplete_iff t).mpr hcomplete) hRic
    (fun s => ULift.up.{u} (γ s)) (fun s r => by
      simpa only [H, F.ulift_edist] using hγ s r)
  constructor
  · intro x
    simpa only [H, F.ulift_scalarCurvature] using hflat.1 (ULift.up.{u} x)
  · intro x
    simpa only [H, F.ulift_curvatureTensorNorm] using hflat.2.2 (ULift.up.{u} x)

theorem not_minimizing_line_of_nonflat_small_surface
    {M : Type} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {J : Set ℝ} (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 2 M J)
    (t : ℝ) (hcomplete : MetricComplete (F.metric t))
    (hoperator : ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hnonflat : ∃ p, 0 < (F.connection t).scalarCurvature p) (γ : ℝ → M) :
    ¬ ∀ s r : ℝ, (F.metric t).edist (γ s) (γ r) = ENNReal.ofReal |s - r| := by
  intro hγ
  obtain ⟨p, hp⟩ := hnonflat
  have hz := (F.small_surface_curvature_eq_zero_of_minimizing_line
    hC t hcomplete hoperator γ hγ).1 p
  exact (ne_of_gt hp) hz

end PoincareConjecture.RicciFlow
