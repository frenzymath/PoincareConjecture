import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.DerivativeControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem terminalFlow_curvatureDerivativeNorm_of_ne
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ≠ T) (k : ℕ) (x : H.regularRegion P04) :
    ((H.terminalFlow P04).connection t).curvatureDerivativeNorm k x =
      (H.reference.flow.connection t).curvatureDerivativeNorm k (x : M) := by
  apply ((H.terminalFlow P04).connection t).curvatureDerivativeNorm_eq_pullback
    (H.reference.flow.connection t) (f := Subtype.val) isOpen_univ
    ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (H.regularRegion P04)).contMDiff.contMDiffOn)
    ?_ ?_ k (mem_univ x)
  · intro y _
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  · intro y _ v w
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
    exact H.terminalMetricFamily_inner_of_ne P04 ht y v w



theorem exists_terminalFlow_curvature_derivative_tail_on_compact
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico s T, ∀ x ∈ A,
        ((H.terminalFlow P04).connection t).curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨s, hs, hsT, hbound⟩ := H.exists_uniform_curvature_derivative_tail_on_compact P04
    (hA.image continuous_subtype_val) (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  refine ⟨s, hs, hsT, fun k => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hbound k
  refine ⟨C, hC, fun t ht x hx => ?_⟩
  rw [H.terminalFlow_curvatureDerivativeNorm_of_ne P04 ht.2.ne]
  exact hbound t ht x (mem_image_of_mem _ hx)

end PoincareConjecture.SingularTimeAssumptions
