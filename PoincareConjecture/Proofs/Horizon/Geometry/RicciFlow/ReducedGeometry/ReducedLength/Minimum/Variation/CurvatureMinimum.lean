import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Orthonormal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Minimizer








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variation.Frame

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem curvature_add_minimum_le_two (K : AncientKappaSolution 2 M)
    {τ m : ℝ} (hτ : 0 < τ) (q : BackwardTimePath K.flow 0 0 τ)
    (S : SqrtRegularPath q)
    (E : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) S.curve
      (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ))))
    (hmin : ∀ r : BackwardTimePath K.flow 0 0 τ, r.curve 0 = q.curve 0 →
      backwardLLength K.flow 0 0 τ q.curve ≤ backwardLLength K.flow 0 0 τ r.curve)
    (heuler : ∀ s ∈ Ioo 0 (Real.sqrt τ),
      regularizedLGeodesicEquation K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) E s)
    (hterminal : curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) = 0)
    (haction : backwardLLength K.flow 0 0 τ q.curve = 2 * Real.sqrt τ * m) :
    τ * (K.flow.connection (-τ)).scalarCurvature (S.curve (Real.sqrt τ)) + m ≤ 2 := by
  have hCS : Icc 0 (Real.sqrt τ) ⊆ S.domain := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using S.interval_subset
  obtain ⟨U, P, hU, _, hCU, hUS, hP, horth⟩ :=
    exists_smooth_adapted_orthonormal_frame_surface K.flow S.curve S.domain
      S.open_domain S.smooth (Real.sqrt τ) (Real.sqrt_nonneg τ) hCS
  exact K.curvature_add_minimum_le_two_of_adapted_frame hτ q S E hmin heuler
    hterminal haction U hU hCU (S.smooth.mono hUS) P hP
      (fun s hs ↦ horth s (hCU hs))

end PoincareConjecture.AncientKappaSolution
