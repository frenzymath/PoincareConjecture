import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.TerminalRigidity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Pullback

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold VectorField
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow

theorem curvatureTensorNorm_eq_zero_of_terminal_homothetic_field_small
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    {c : ℝ} (hc : c ≠ 0)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x,
      (F.connection 0).connection V x v = c • v) :
    ∀ x, (F.connection 0).curvatureTensorNorm x = 0 := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} M) :=
    Poincare.Manifold.uliftChartedSpace _ M
  let : IsManifold (𝓡 n) ∞ (ULift.{u} M) :=
    Poincare.Manifold.uliftIsManifold (𝓡 n) M
  let e := Poincare.Manifold.uliftDiffeomorph (𝓡 n) M
  let H : RicciFlow n (ULift.{u} M) (Iic 0) := F.ulift
  have hinv (x : ULift.{u} M) : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible :=
    ⟨e.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩
  let W := mpullback (𝓡 n) (𝓡 n) e V
  have hW : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) :=
    hVsmooth.mpullback_vectorField e.contMDiff hinv (by simp)
  have hparallel (x : ULift.{u} M) (v : TangentSpace (𝓡 n) x) :
      (H.connection 0).connection W x v = c • v := by
    rw [(H.connection 0).connection_mpullback_of_metric_pullback
      (F.connection 0) (e.contMDiff x) (Eventually.of_forall hinv)
      (Eventually.of_forall (fun _ _ _ => rfl))
      (hVsmooth.mdifferentiable (by simp) (e x)) v, hV]
    rw [map_smul, (hinv x).inverse_apply_self]
  have hzero := H.curvatureTensorNorm_eq_zero_of_terminal_homothetic_field
    hC (fun t ht x => (F.ulift_nonnegativeCurvatureOperator_iff t x).mpr
      (hoperator t ht x.down)) W hW hc hparallel
  intro x
  simpa only [H, F.ulift_curvatureTensorNorm] using hzero (ULift.up.{u} x)

end PoincareConjecture.RicciFlow
