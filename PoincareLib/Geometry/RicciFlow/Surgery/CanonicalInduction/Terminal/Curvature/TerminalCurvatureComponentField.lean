import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Curvature.TerminalCurvatureOpenInclusion
import PoincareLib.Geometry.Riemannian.Metric.ConnectedComponent
import PoincareLib.Geometry.Riemannian.Connection.Construction

/-!
# The actual parallel field on a connected cover component

The literal open-inclusion pullback retains the vector, its unit norm,
and its zero covariant derivative. Closedness of the component retains
metric completeness.
Source: derivations/terminal-curvature-parallel-flow.md, Stage C6b.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M47

open Poincare.Geometry.Manifold.RegularLevel

/-- Restrict an actual complete parallel unit field to the actual
connected component, preserving its coordinate vector at each point. -/
theorem terminalCurvature_component_field
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (hg : MetricComplete g)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hunit : ∀ x, g.inner x (V x) (V x) = 1)
    (hparallel : ∀ x v, D.connection V x v = 0) (p : M) :
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    let gC := g.connectedComponentMetric p
    let W := mpullback (𝓡 n) (𝓡 n) (Subtype.val : C → M) V
    ConnectedSpace C ∧ MetricComplete gC ∧
      ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) ∧
      ∀ x : C, W x = V x.val ∧ gC.inner x (W x) (W x) = 1 ∧
        ∀ v, gC.leviCivitaData.connection W x v = 0 := by
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let gC := g.connectedComponentMetric p
  let W := mpullback (𝓡 n) (𝓡 n) (Subtype.val : C → M) V
  have hi := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) C
  have hinv (x : C) : (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : C → M) x).IsInvertible :=
    ⟨hi.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩
  have hm (x : C) (v w : TangentSpace (𝓡 n) x) :
      gC.inner x v w = g.inner x.val
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : C → M) x v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : C → M) x w) := rfl
  have hmetric (x : C) (v w : TangentSpace (𝓡 n) x) :
      gC.inner x v w = g.inner x.val v w := by
    simpa only [mfderiv_opens_subtypeVal_apply] using hm x v w
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · exact RiemannianMetric.metricComplete_of_subtype_val isClosed_connectedComponent
      g gC hm hg
  · intro x
    exact (hV x.val).mpullback_vectorField_preimage
      (hi.contMDiff x) (hinv x) (by simp)
  · intro x
    have heq : W x = V x.val := terminalCurvature_open_mpullback C V x
    refine ⟨heq, ?_, ?_⟩
    · rw [hmetric]
      exact (congrArg (fun z : EuclideanSpace ℝ (Fin n) => g.inner x.val z z) heq).trans
        (hunit x.val)
    · intro v
      rw [terminalCurvature_open_connection D C gC.leviCivitaData hmetric V x
        ((hV x.val).mdifferentiableAt (by simp))]
      exact hparallel x.val v

end PoincareMT.M47
