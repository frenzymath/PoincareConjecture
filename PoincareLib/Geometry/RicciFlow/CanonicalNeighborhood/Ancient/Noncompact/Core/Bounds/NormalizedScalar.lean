import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services

/-!
# Local scalar bounds in every carrier universe

Transport the normalized compactness bound through the existing small based
solution. This supplies the scalar estimate for the soul-centered core using
only the shared analytic services.

Reference: Morgan--Tian, Proposition 9.85(1), pp. 237--239.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

theorem noncompact_uniform_scalar_bound_of_normalized
    (P : NoncompactKappaServices.{u})
    {kappa r : ℝ} (hkappa : 0 < kappa) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ∀ x ∈ (K.flow.metric 0).ball p r,
          (K.flow.connection 0).scalarCurvature x ≤ C := by
  obtain ⟨C, hC, hbound⟩ := ScalarDerivatives.uniform_based_local_scalar_bound
    P.toScalarDerivativeServices hkappa r hr
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnc hnormalized x hx
  have hb := hbound
    (ScalarDerivatives.smallBasedKappaSolution K p kappa hkappa hnc hnormalized)
    (equivShrink M x)
    ((ScalarDerivatives.smallBasedKappaSolution_mem_ball K p kappa hkappa hnc hnormalized
      0 r x).mpr hx)
  change (K.flow.shrink.connection 0).scalarCurvature (equivShrink M x) ≤ C at hb
  simpa only [K.flow.shrink_scalarCurvature, Equiv.symm_apply_apply] using hb

end PoincareMT
