import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.BoundedDistanceInputs
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants

/-!
# Scalar continuity on the actual generalized spacetime

Local isometry invariance identifies the supplied slice connection's scalar
with the ordinary scalar in each original flow box. M04 joint regularity
and the open box cover then give continuity on the actual sigma spacetime,
including included time endpoints. This supplies scalar transport in the
reviewed dense-time form of Theorem 10.2; see task derivation 08.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

/-- Original flow-box scalar curvature equals the scalar of the actual
slice connection; Morgan--Tian Definitions 3.34-3.38, printed pp. 59-61. -/
theorem GeneralizedRicciFlowData.scalar_box
    (F : GeneralizedRicciFlowData.{u}) (b : F.box_index)
    (t : ℝ) (ht : t ∈ (F.box b).interval) (x : (F.box b).carrier.carrier) :
    F.scalar ⟨t, (F.box b).forward t ht x⟩ =
      ((F.box b).flow.connection t).scalarCurvature x := by
  symm
  exact ((F.box b).flow.connection t).scalarCurvature_eq_of_local_isometry
    (F.connection t) isOpen_univ ((F.box b).forward_smooth t ht).contMDiffOn
    (fun y _ v w => ((F.box b).metric_pullback t ht y v w).symm) (mem_univ x)

/-- M04 scalar regularity is continuous on the product of the actual time
interval and spatial carrier, including endpoints (task derivation 08). -/
theorem RicciFlow.continuous_scalar_parameter
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (G : RicciFlow n M J) (P : RicciFlowCurvatureTheory.{u}) :
    Continuous (fun z : J × M => (G.connection z.1.1).scalarCurvature z.2) := by
  have hscalar : ContinuousOn
      (fun z : ℝ × M => (G.connection z.1).scalarCurvature z.2) (J ×ˢ univ) :=
    (P.scalar_regular n M J G).continuousOn
  have hmap : Continuous (fun z : J × M => (z.1.val, z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact hscalar.comp_continuous (f := fun z : J × M => (z.1.val, z.2)) hmap
    (fun z => ⟨z.1.property, mem_univ z.2⟩)

/-- The actual generalized scalar is continuous on the entire spacetime,
including relative time endpoints, as used in the dense-time form of
Morgan--Tian Theorem 10.2 (task derivation 08). -/
theorem GeneralizedRicciFlowData.continuous_scalar_m28
    (F : GeneralizedRicciFlowData.{u}) (P : RicciFlowCurvatureTheory.{u}) :
    Continuous F.scalar := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, x⟩
  obtain ⟨b, ht, y, rfl⟩ := F.box_covers t x
  apply ((F.box_openEmbedding b).continuousAt_iff
    (x := (⟨t, ht⟩, y)) (g := F.scalar)).mp
  have hR := (F.box b).flow.continuous_scalar_parameter P
  simpa only [Function.comp_def, F.scalar_box] using
    hR.continuousAt (x := (⟨t, ht⟩, y))

/-- Scalar curvature is jointly continuous in the time and spatial variables
of every actual generalized cylinder, including its included endpoints.
This is the scalar producer in the dense-time argument (task derivation 08). -/
theorem GeneralizedFlowCylinder.continuous_scalar
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (P : RicciFlowCurvatureTheory.{u}) :
    Continuous (fun z : I × U => F.scalar (e.pointMap z.1.1 z.1.2 z.2.1)) :=
  (F.continuous_scalar_m28 P).comp e.embedding.continuous

end PoincareMT
