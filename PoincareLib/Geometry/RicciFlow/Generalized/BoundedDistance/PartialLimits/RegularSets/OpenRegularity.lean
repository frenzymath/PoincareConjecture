import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.OpenCapture

/-!
# Regularity and volume through nested open regions

Definition 5.1 of Morgan--Tian, printed p. 83, descends through actual
open inclusion: compact intrinsic ball closures have compact ambient
images containing the ambient balls supplied by OpenCapture. Applying
the exact volume identity twice handles the critical region inside the
already normalized tube. See the critical-region-noncollapse derivation
dated 2026-09-24 under tasks/M28/review-endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Intrinsic regularity in an open region gives ambient regularity at
the same radius, by compact images of the smaller ball closures. -/
theorem regularPoints_of_intrinsicOpenMetric
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p : U)
    {r : ℝ} (hp : p ∈ regularPoints (intrinsicOpenMetric g U) r) :
    (p : M) ∈ regularPoints g r := by
  intro s hsr
  let K := (Subtype.val : U → M) '' closure ((intrinsicOpenMetric g U).ball p s)
  have hK : IsCompact K := (hp s hsr).image continuous_subtype_val
  have hball : g.ball (p : M) s ⊆ K := by
    rw [← intrinsicOpenMetric_ball_image_of_regular g U p
      (regularPoints_antitone (intrinsicOpenMetric g U) hsr.le hp)]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, subset_closure hx, rfl⟩
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hball hK.isClosed)

/-- At an intrinsically regular point of two nested open regions, inclusion
maps the entire regular ball onto the ambient ball. This is the finite-path
capture used in Claim 10.6, printed p. 252; see M28 derivation 70. -/
theorem nested_intrinsicOpenMetric_ball_image_of_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens U) (p : V) {r : ℝ}
    (hp : p ∈ regularPoints (intrinsicOpenMetric (intrinsicOpenMetric g U) V) r) :
    (fun q : V => ((q : U) : M)) ''
        (intrinsicOpenMetric (intrinsicOpenMetric g U) V).ball p r =
      g.ball ((p : U) : M) r := by
  calc
    _ = (Subtype.val : U → M) ''
        ((Subtype.val : V → U) ''
          (intrinsicOpenMetric (intrinsicOpenMetric g U) V).ball p r) := by
      rw [Set.image_image]
    _ = (Subtype.val : U → M) '' (intrinsicOpenMetric g U).ball (p : U) r := by
      rw [intrinsicOpenMetric_ball_image_of_regular (intrinsicOpenMetric g U) V p hp]
    _ = g.ball ((p : U) : M) r :=
      intrinsicOpenMetric_ball_image_of_regular g U (p : U)
        (regularPoints_of_intrinsicOpenMetric (intrinsicOpenMetric g U) V p hp)

variable [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]

/-- A regular ball in two actual nested open restrictions has the volume
of the ambient ball; both capture statements follow from regularity. -/
theorem nested_intrinsicOpenMetric_ball_volume_of_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens U) (p : V) {r : ℝ}
    (hp : p ∈ regularPoints (intrinsicOpenMetric (intrinsicOpenMetric g U) V) r) :
    (intrinsicOpenMetric (intrinsicOpenMetric g U) V).volumeMeasure
        ((intrinsicOpenMetric (intrinsicOpenMetric g U) V).ball p r) =
      g.volumeMeasure (g.ball ((p : U) : M) r) := by
  rw [intrinsicOpenMetric_ball_volume_of_regular (intrinsicOpenMetric g U) V p hp]
  exact intrinsicOpenMetric_ball_volume_of_regular g U (p : U)
    (regularPoints_of_intrinsicOpenMetric (intrinsicOpenMetric g U) V p hp)

end PoincareMT.M28
