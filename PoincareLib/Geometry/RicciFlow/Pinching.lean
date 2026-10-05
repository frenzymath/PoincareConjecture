import PoincareLib.Geometry.RicciFlow.Pinching.Assembly
import PoincareLib.Geometry.RicciFlow.Pinching.Conclusion
import PoincareLib.Geometry.RicciFlow.Pinching.GeometricPreservation.Preservation

/-!
# Hamilton--Ivey pinching persistence

The reviewed M05 statement follows from compact geometric barrier preservation,
the scalar maximum principle, and the geometric three-spectrum.

Reference: Morgan--Tian, Claims 4.28--4.31, pp. 77--79;
Theorem 4.32, pp. 79--80, and Corollary 4.33, p. 80.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem hamiltonIveyPinching
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hinit : HamiltonIveyPinchedAt (F.connection a) a) :
    HamiltonIveyPinchingConclusion a b F := by
  have hlog : ∀ t ∈ Set.Ico a b, ∀ x : M,
      0 < (F.connection t).negativeCurvaturePart x →
        2 * (F.connection t).negativeCurvaturePart x *
            (Real.log ((F.connection t).negativeCurvaturePart x) +
              Real.log (1 + t) - 3) ≤
          (F.connection t).scalarCurvature x := by
    exact (RicciFlow.Frame.hamiltonIvey_pinching_persists ha hab F hM04
      hinit.2.1 hinit.2.2).2
  have hbounds := pinching_persistence_and_bounds_of_log ha hab F hM04 hinit.2.1 hlog
  exact
    { persistence := fun t ht => ⟨ha.trans ht.1, hbounds.1 t ht, hlog t ht⟩
      spectral_bridge := hbounds.2.1
      full_norm_bound := hbounds.2.2
      full_norm_bound_continuous := continuous_const.mul (continuous_id.max continuous_const) }

end PoincareMT
