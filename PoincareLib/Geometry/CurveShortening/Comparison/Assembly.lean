import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Static.Approximation
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Family.ApproximationFromStatic
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Disk.ComparisonComplete
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Finite.NetsComplete
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Flow.ConclusionAssembly

/-!
# Closed approximation and three-dimensional packaging

The static approximation theorem supplies the raw family at the exact
initial metric and connection.  M63's supplied-family clause then turns each
raw family into the evolving approximation consumed by M64.  The disk and
finite-net fields are direct products of the already proved comparison
constructors once an actual M64 flow conclusion has been supplied.

Morgan--Tian context: Chapter 19, Sections 19.3-19.7, printed pp. 447-481; the frozen M64
contracts and project comparison erratum specify the final interfaces.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}

/-- Apply M63's supplied-family conclusion to every raw M64 approximation from the closed
static raw-family supplier. Source: Assembly of MT Lemmas 19.15, 19.30 and 19.31, pp.
447-449 and 462, in the frozen M64 contract. -/
theorem m64FamilyApproximationTheory_of_M63
    (hM63 : M63RampEstimatesTheory.{u})
    (hcompact : IsCompact (Set.univ : Set M))
    (analytic : M63AnalyticConclusion F G) :
    M64FamilyApproximationTheory F G := by
  apply m64FamilyApproximationTheory_from_static_raw hM63 hcompact analytic
  intro Gamma hnull zeta hzeta
  exact (m64StaticApproximationTheory_of_compact (F.metric a) (F.connection a)
    hcompact).raw_family Gamma hnull zeta hzeta

/-- The three-dimensional record is obtained by applying the closed disk and finite-net
constructors to an already supplied M64 flow record. Source: Assembly of MT Lemmas 19.15,
19.30 and 19.31, pp. 447-449 and 462, in the frozen M64 contract. -/
theorem m64ThreeDimensionalFlowConclusion_of_flow_M63
    (hM63 : M63RampEstimatesTheory.{u})
    (hcompact : IsCompact (Set.univ : Set M))
    (flow : M64FlowConclusion F)
    (analytic : M63AnalyticConclusion F flow.geometry) :
    Nonempty (M64ThreeDimensionalFlowConclusion F) := by
  let approximation := m64FamilyApproximationTheory_of_M63 hM63 hcompact
    analytic
  let disks : ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
      M64DiskAreaComparison (flow.geometry.product circumference h) t :=
    fun circumference h t ht => m64DiskAreaComparison_of_product
      (flow.geometry.product circumference h) t
  let finite_nets := m64FamilyAnnulusNets_of_compact flow.geometry hcompact
  exact m64ThreeDimensionalFlowConclusion_of_fields flow approximation disks finite_nets

end PoincareMT
